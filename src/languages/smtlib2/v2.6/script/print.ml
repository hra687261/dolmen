
(* This file is free software, part of dolmen. See file "LICENSE" for more information *)

(* Printing of identifiers *)
(* ************************************************************************* *)

exception Cannot_print of string

let _cannot_print format =
  Format.kasprintf (fun msg -> raise (Cannot_print msg)) format

(* lexical definitions taken from the smtlib specification *)

let[@inline] is_whitespace c =
  let c = Char.code c in
  c = 9 (* tab *) || c = 10 (* line feed *) ||
  c = 13 (* cariage return *) || c = 32 (* space *)

let[@inline] is_printable c =
  let c = Char.code c in
  (32 <= c && c <= 126) || 128 <= c

let is_quoted_symbol_char c =
  (is_whitespace c || is_printable c) &&
  (c <> '|' && c <> '\\')

let[@inline] is_letter = function
  | 'a'..'z' | 'A'..'Z' -> true
  | _ -> false

let[@inline] is_digit = function
  | '0'..'9' -> true
  | _ -> false

let[@inline] is_other_simple_symbol_chars = function
  | '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_'
  | '-' | '+' | '=' | '<' | '>' | '.' | '?' | '/' -> true
  | _ -> false

let is_simple_symbol_char c =
  is_letter c || is_digit c || is_other_simple_symbol_chars c

(* symbol categorization *)

type symbol =
  | Simple
  | Quoted
  | Unprintable

let categorize_symbol s =
  match s with
  | "" -> Unprintable
  | "_" | "!" | "as" | "let"
  | "exists" | "forall"
  | "match" | "par"
  | "assert"
  | "check-sat"
  | "check-sat-assuming"
  | "declare-const"
  | "declare-datatype"
  | "declare-datatypes"
  | "declare-fun"
  | "declare-sort"
  | "define-fun"
  | "define-fun-rec"
  | "define-funs-rec"
  | "define-sort"
  | "echo"
  | "exit"
  | "get-assertions"
  | "get-assignment"
  | "get-info"
  | "get-model"
  | "get-option"
  | "get-proof"
  | "get-unsat-assumptions"
  | "get-unsat-core"
  | "get-value"
  | "pop"
  | "push"
  | "reset"
  | "reset-assertions"
  | "set-info"
  | "set-logic"
  | "set-option" -> Quoted
  | _ ->
    (* we are guaranteed that `s` is not the empty string *)
    if not (is_digit s.[0]) &&
       (Dolmen_std.Misc.string_for_all is_simple_symbol_char s) then
      Simple
    else if Dolmen_std.Misc.string_for_all is_quoted_symbol_char s then
      Quoted
    else
      Unprintable

let id_aux fmt s =
  (* TODO: expose/add a cache to not redo the `categorize_symbol` computation each time *)
  match categorize_symbol s with
  | Simple -> Format.pp_print_string fmt s
  | Quoted -> Format.fprintf fmt "|%s|" s
  | Unprintable ->
    _cannot_print "symbol \"%s\" cannot be printed due to lexical constraints" s

let id fmt name =
  match (name : Dolmen_std.Name.t) with
  | Simple s ->
    id_aux fmt s
  | Indexed { basename = _; indexes = [] } ->
    _cannot_print "indexed id with no indexes: %a" Dolmen_std.Name.print name
  | Indexed { basename; indexes; } ->
    let pp_sep fmt () = Format.fprintf fmt " " in
    Format.fprintf fmt "(_ %a %a)"
      id_aux basename (Format.pp_print_list ~pp_sep id_aux) indexes
  | Qualified _ ->
    _cannot_print "qualified identifier: %a" Dolmen_std.Name.print name


(* sanitization *)

let sanitize_aux _idx = function
  (* smtlib identifiers can be quoted, and quotable symbols are a strict
     superset of non-quoted symbols, so we only need to make sure that
     all characters are quotable *)
  | None -> [Uchar.of_char '_']
  | Some c ->
    if Uchar.is_char c &&
       is_quoted_symbol_char (Uchar.to_char c) then
      [c]
    else
      [Uchar.of_char '_']

let sanitize _id name =
  match (name : Dolmen_std.Name.t) with
  | Simple "" ->
    Dolmen_std.Name.simple "_"
  | Simple s ->
    let s' = Dolmen_std.Misc.string_unicode_map sanitize_aux s in
    (* avoid an allocation if the name has not changed *)
    if s' == s then name else Dolmen_std.Name.simple s'
  | Indexed { basename = basename; indexes; } ->
    let basename' = Dolmen_std.Misc.string_unicode_map sanitize_aux basename in
    let indexes' =
      Dolmen_std.Misc.list_map_sharing
      (Dolmen_std.Misc.string_unicode_map sanitize_aux) indexes
    in
    if basename == basename' && indexes = indexes'
    then name
    else Dolmen_std.Name.indexed basename' indexes'
  | Qualified _ ->
    (* TODO: proper error ? Related to how dolmen will handle translation
       between languages with multiple files / qualified includes... *)
    assert false

let string fmt s =
  let can_print = ref true in
  let quotation = ref 0 in
  String.iter (fun c ->
      if c = '"' then quotation := !quotation + 1;
      if not (is_whitespace c || is_printable c) then can_print := false
    ) s;
  if not !can_print then
    _cannot_print "string: \"%s\"" s
  else if !quotation = 0 then
    Format.pp_print_string fmt s
  else begin
    String.iter (function
        | '"' -> Format.fprintf fmt {|""|}
        | c -> Format.fprintf fmt "%c" c) s
  end



(* Printing of terms and statements *)
(* ************************************************************************* *)

module Make
    (Env : Dolmen_intf.Env.Print
     with type name := Dolmen_std.Name.t)
    (V : Dolmen_intf.View.FO.S
     with type ty := Env.ty
      and type ty_var := Env.ty_var
      and type ty_cst := Env.ty_cst
      and type term := Env.term
      and type term_var := Env.term_var
      and type term_cst := Env.term_cst)
= struct

  module N = Dolmen_std.Name
  module B = Dolmen_std.Builtin

  (* Helpers *)
  (* ******* *)

  let list pp env fmt l =
    let pp_sep fmt () = Format.fprintf fmt "@ " in
    Format.pp_print_list ~pp_sep (pp env) fmt l


  (* Ids *)
  (* *** *)

  let id _env fmt name = id fmt name


  (* Types *)
  (* ***** *)

  let ty_head_name env head =
    match (head : _ Dolmen_intf.View.FO.head) with
    | Cst c -> Env.Ty_cst.name env c
    | Builtin B.Prop -> N.simple "Bool"
    | Builtin _ -> assert false

  let rec ty env fmt t =
    match V.Ty.view t with
    | Var v -> ty_var env fmt v
    | App (head, args) ->
      let f = ty_head_name env head in
      begin match args with
        | [] ->
          id env fmt f
        | _ :: _ ->
          Format.fprintf fmt "(%a %a)"
            (id env) f (ty_args env) args
      end

  and ty_var env fmt v =
      let name = Env.Ty_var.name env v in
      (* TODO: setup a cache from names to category in one of the env's keys *)
      id env fmt name

  and ty_cst env fmt c =
    let name = Env.Ty_cst.name env c in
    id env fmt name

  and ty_args env fmt l =
    list ty env fmt l


  (* Terms *)
  (* ***** *)

  let term _env _fmt (_t : Env.term) = assert false

  and term_var _env _fmt _v = assert false

  and term_cst _env _fmt (_c : Env.term_cst) = assert false

  and attribute _env _fmt _t =
    (* same as `term` but check that it is the application of a keyword,
       i.e. a symbol that starts with ':' *)
    assert false

  and keyword _env _fmt _t =
    assert false

  and prop_literal _env _fmt _t =
    (* either 'c' or 'not c' with 'c' a constant *)
    assert false



  (* Statements *)
  (* ********** *)

  (* unit/trivial statements *)

  let unit_stmt s (_env : Env.t) fmt () =
    Format.fprintf fmt "(%s)" s

  let check_sat = unit_stmt "check-sat"

  let reset = unit_stmt "reset"
  let reset_assertions = unit_stmt "reset-assertions"

  let get_unsat_core = unit_stmt "get-unsat-core"
  let get_unsat_assumptions = unit_stmt "get-unsat-assumptions"

  let get_proof = unit_stmt "get-proof"
  let get_model = unit_stmt "get-model"

  let get_assertions = unit_stmt "get-assertions"
  let get_assignment = unit_stmt "get-assignment"

  let exit = unit_stmt "exit"

  (* statements with payloads *)

  let echo _env fmt s =
    Format.fprintf fmt "(echo \"%a\")" string s

  let set_logic _env fmt s =
    Format.fprintf fmt "(set-logic %a)" id_aux s

  let set_info env fmt t =
    Format.fprintf fmt "(set-info %a)" (attribute env) t

  let set_option env fmt t =
    Format.fprintf fmt "(set-option %a)" (attribute env) t

  let get_info env fmt t =
    Format.fprintf fmt "(get-info %a)" (keyword env) t

  let get_option env fmt t =
    Format.fprintf fmt "(get-option %a)" (keyword env) t

  let get_value env fmt l =
    Format.fprintf fmt "@[<hv 2>(get-value (@,@[<hv>%a@]@,))"
      (list term env) l

  let pop _env fmt n =
    if n <= 0
    then raise (Cannot_print "pop with non-positive level")
    else Format.fprintf fmt "(pop %d)" n

  let push _env fmt n =
    if n <= 0
    then raise (Cannot_print "push with non-positive level")
    else Format.fprintf fmt "(push %d)" n

  let declare_sort env fmt c =
    let n = V.Ty.Cst.arity c in
    let name = Env.Ty_cst.name env c in
    Format.fprintf fmt "(declare-sort %a %d)" (id env) name n

  let declare_fun env fmt c =
    let name = Env.Term_cst.name env c in
    let c_sig = V.Term.Cst.ty c in
    match V.Sig.view c_sig with
    | Signature ([], [], c_ty) ->
      Format.fprintf fmt "(declare-const %a %a)"
        (id env) name (ty env) c_ty
    | Signature ([], params, ret) ->
      Format.fprintf fmt "(declare-fun %a (%a) %a)"
        (id env) name (ty_args env) params (ty env) ret
    | Signature (_ :: _, _, _) ->
      (* TODO: proper error, polymorphic functions are not supported in smtlib v2.6 *)
      assert false

  let define_sort env fmt (c, params, body) =
    let env = List.fold_left Env.Ty_var.bind env params in
    Format.fprintf fmt "(define-sort %a (%a) %a)"
      (ty_cst env) c
      (list ty_var env) params
      (ty env) body

  let define_fun_aux ~recursive env fmt (f, params, ret_ty, body) =
    let env = List.fold_left Env.Term_var.bind env params in
    Format.fprintf fmt "(%s %a (%a) %a %a)"
      (if recursive then "define-fun-rec" else "define-fun")
      (term_cst env) f
      (list term_var env) params
      (ty env) ret_ty
      (term env) body

  let define_fun = define_fun_aux ~recursive:false
  let define_fun_rec = define_fun_aux ~recursive:true

  let define_funs_rec env fmt l =
    let fun_body env fmt (_, _, _, body) = term env fmt body in
    let fun_decl env fmt (f, params, ret_ty, _) =
      Format.fprintf fmt "(%a (%a) %a)"
        (term_cst env) f
        (list term_var env) params
        (ty env) ret_ty
    in
    Format.fprintf fmt
      "@[<v 2>(define-funs-rec@ @[<v 2>(%a)@]@ @[<v 2>(%a)@])@]"
      (list fun_decl env) l
      (list fun_body env) l

  let assert_ env fmt t =
    Format.fprintf fmt "(assert %a)" (term env) t

  let check_sat_assuming env fmt = function
    | [] -> check_sat env fmt ()
    | _ :: _ as l ->
      Format.fprintf fmt "(check-sat-assuming (%a))"
        (list prop_literal env) l

end

