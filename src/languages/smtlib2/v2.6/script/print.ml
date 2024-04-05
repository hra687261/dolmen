
(* This file is free software, part of dolmen. See file "LICENSE" for more information *)

(* Printing of identifiers *)
(* ************************************************************************* *)

module Misc = Dolmen_std.Misc

exception Cannot_print of string

(* TODO: structured errors *)
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

let[@inline] is_quoted_symbol_char c =
  (is_whitespace c || is_printable c) &&
  (c <> '|' && c <> '\\')

(* symbol categorization *)

type symbol =
  | Simple
  | Quoted
  | Unprintable

let categorize_symbol s =
  if String.length s = 0 (* s = "" *) then
    Unprintable
  else begin
    match Lexer.M.find_opt s Lexer.reserved_words with
    | Some _ -> Quoted
    | None ->
      if Misc.lex_string Lexer.check_simple_symbol s then
        Simple
      else if Misc.lex_string Lexer.check_quoted_symbol s then
        Quoted
      else
        Unprintable
  end

let symbol_aux fmt s =
  (* TODO: expose/add a cache to not redo the `categorize_symbol` computation each time *)
  match categorize_symbol s with
  | Simple -> Format.pp_print_string fmt s
  | Quoted -> Format.fprintf fmt "|%s|" s
  | Unprintable ->
    _cannot_print "symbol \"%s\" cannot be printed due to lexical constraints" s

let symbol fmt name =
  match (name : Dolmen_std.Name.t) with
  | Simple s ->
    symbol_aux fmt s
  | Indexed { basename = _; indexes = [] } ->
    _cannot_print "indexed id with no indexes: %a" Dolmen_std.Name.print name
  | Indexed { basename; indexes; } ->
    let pp_sep fmt () = Format.fprintf fmt " " in
    Format.fprintf fmt "(_ %a %a)"
      symbol_aux basename (Format.pp_print_list ~pp_sep symbol_aux) indexes
  | Qualified _ ->
    _cannot_print "qualified identifier: %a" Dolmen_std.Name.print name

let keyword fmt name =
  match (name : Dolmen_std.Name.t) with
  | Simple s when Misc.lex_string Lexer.check_keyword s ->
    Format.pp_print_string fmt s
  | _ -> _cannot_print "not a keyword"

let num fmt s =
  if Misc.lex_string Lexer.check_num s then
    Format.pp_print_string fmt s
  else
    _cannot_print "num"

let dec fmt s =
  if Misc.lex_string Lexer.check_dec s then
    Format.pp_print_string fmt s
  else
    _cannot_print "dec"

let hex fmt s =
  if Misc.lex_string Lexer.check_hex s then
    Format.pp_print_string fmt s
  else
    _cannot_print "hex"

let bin fmt s =
  if Misc.lex_string Lexer.check_bin s then
    Format.pp_print_string fmt s
  else
    _cannot_print "bin"

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
    Format.fprintf fmt {|"%s"|} s
  else begin
    Format.pp_print_char fmt '"';
    String.iter (function
        | '"' -> Format.fprintf fmt {|""|}
        | c -> Format.fprintf fmt "%c" c) s;
    Format.pp_print_char fmt '"'
  end

(* sanitization *)

let sanitize_aux _idx o =
  (* smtlib identifiers can be quoted, and quotable symbols are a strict
     superset of non-quoted symbols, so we only need to make sure that
     all characters are quotable *)
  match o with
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
    _cannot_print "qualified names in smtlib2"


(* Printing of terms and statements *)
(* ************************************************************************* *)

module Make
    (Env : Dolmen_intf.Env.Print
     with type name := Dolmen_std.Name.t)
    (S : Dolmen_intf.View.Sexpr.S
     with type id := Dolmen_std.Id.t)
    (V : Dolmen_intf.View.TFF.S
     with type ty = Env.ty
      and type ty_var = Env.ty_var
      and type ty_cst = Env.ty_cst
      and type term = Env.term
      and type term_var = Env.term_var
      and type term_cst = Env.term_cst
      and type formula = Env.formula)
= struct

  module N = Dolmen_std.Name
  module B = Dolmen_std.Builtin
  module F = Dolmen_intf.View.TFF
  module E = Dolmen_std.View.Assoc(V)

  (* Helpers *)
  (* ******* *)

  let list pp env fmt l =
    let pp_sep fmt () = Format.fprintf fmt "@ " in
    Format.pp_print_list ~pp_sep (pp env) fmt l


  (* Ids *)
  (* *** *)

  let symbol _env fmt name = symbol fmt name

  let id ~allow_keyword env fmt id =
    match (id : Dolmen_std.Id.t) with
    | { ns = Value String; name = Simple s; } -> string fmt s
    | { ns = Value Integer; name = Simple s; } -> num fmt s
    | { ns = Value Real; name = Simple s; } -> dec fmt s
    | { ns = Value Hexadecimal; name = Simple s; } -> hex fmt s
    | { ns = Value Binary; name = Simple s; } -> bin fmt s
    | { ns = (Attr | Term); name = Simple s; } ->
      if (allow_keyword && Misc.lex_string Lexer.check_keyword s)
         || Misc.lex_string Lexer.check_simple_symbol s then
        Format.pp_print_string fmt s
      else if Misc.lex_string Lexer.check_quoted_symbol s then
        Format.fprintf fmt "|%s|" s
      else
        _cannot_print "unprintable symbol"
    | { ns = Term; name; } ->
      symbol env fmt name
    | _ ->
      _cannot_print "unprintable id"


  (* Types *)
  (* ***** *)

  let ty_var env fmt v =
    let name = Env.Ty_var.name env v in
    (* TODO: setup a cache from names to category in one of the env's keys *)
    symbol env fmt name

  let ty_cst env fmt c =
    let name = Env.Ty_cst.name env c in
    (* TODO: setup a cache from names to category in one of the env's keys *)
    symbol env fmt name

  let ty_head_name env c =
    (* TODO: add reservations for the builtin names in the env *)
    let int = string_of_int in
    match V.Ty.Cst.builtin c with
    | B.Base -> Env.Ty_cst.name env c
    | B.Prop -> N.simple "Bool"
    | B.Int -> N.simple "Int"
    | B.Real -> N.simple "Real"
    | B.Array -> N.simple "Array"
    | B.Bitv n -> N.indexed "Bitvec" [int n]
    | B.Float (5, 11) -> N.simple "Float16"
    | B.Float (8, 24) -> N.simple "Float32"
    | B.Float (11,53) -> N.simple "Float64"
    | B.Float (15,113) -> N.simple "Float128"
    | B.Float (e, s) -> N.indexed "FloatingPoint" [int e; int s]
    | B.RoundingMode -> N.simple "RoundingMode"
    | B.String -> N.simple "String"
    | B.String_RegLan -> N.simple "RegLan"
    | _ -> _cannot_print "unknown type builtin"

  let rec ty env fmt t =
    match V.Ty.view t with
    | Var v -> ty_var env fmt v
    | App (head, args) ->
      let f = ty_head_name env head in
      begin match args with
        | [] ->
          symbol env fmt f
        | _ :: _ ->
          Format.fprintf fmt "(%a %a)"
            (symbol env) f (list ty env) args
      end


  (* Terms *)
  (* ***** *)

  let term_var env fmt v =
    let name = Env.Term_var.name env v in
    (* TODO: setup a cache from names to category in one of the env's keys *)
    symbol env fmt name

  let term_cst env fmt c =
    let name = Env.Term_cst.name env c in
    (* TODO: setup a cache from names to category in one of the env's keys *)
    symbol env fmt name

  let sorted_var env fmt v =
    Format.fprintf fmt "(%a %a)" (term_var env) v (ty env) (V.Term.Var.ty v)

  let add_binding_to_env env (v, _) =
    Env.Term_var.bind env v

  let add_pattern_to_env env pat =
    match (pat : _ F.Term.pattern) with
    | Var v -> Env.Term_var.bind env v
    | Constructor (_, l) -> List.fold_left Env.Term_var.bind env l

  let term_cst_chainable _env c =
    match V.Term.Cst.builtin c with
    | B.Base -> `Nope
    | B.Equal -> `Chainable (fun c ->
        match V.Term.Cst.builtin c with B.Equal -> true | _ -> false)
    | _ -> `Nope

  let term_cst_assoc _env c =
    match V.Term.Cst.builtin c with
    | B.Base -> `None
    | B.Or -> `Left_assoc (fun c ->
        match V.Term.Cst.builtin c with B.Or -> true | _ -> false)
    | B.And -> `Left_assoc (fun c ->
        match V.Term.Cst.builtin c with B.And -> true | _ -> false)
    | B.Xor -> `Left_assoc (fun c ->
        match V.Term.Cst.builtin c with B.Xor -> true | _ -> false)
    | B.Imply -> `Right_assoc (fun c ->
        match V.Term.Cst.builtin c with B.Imply -> true | _ -> false)
    | _ -> `None

  let term_cst_poly _env c =
    match V.Sig.view (V.Term.Cst.ty c) with
    | Signature (_ :: _, _, _) -> true
    | _ -> false

  (* Note: unfortunately, most of the smtlib term constructions end with a
     parenthesis, and therefore their printers are currently not tail-rec.
     This is particularly true for sequential let-bindings.

     This means that the current printers are likely to produce a stack
     overflow if used on extremely big/deep terms (or with a lot of sequential
     let bindings). We might want to consider ocaml 5 and lifting the stack
     limit for these cases. *)
  let rec term env fmt t =
    term_view env fmt (V.Term.ty t) (V.Term.view t)

  and term_view env fmt t_ty view =
    match (view : _ F.Term.view) with
    | Var v -> term_var env fmt v
    | App (head, _, args) -> term_app env fmt (t_ty, head, args)
    | Match (scrutinee, cases) -> term_match env fmt (scrutinee, cases)
    | Binder (Exists (tys, ts), body) -> quant "exists" env fmt (tys, ts, body)
    | Binder (Forall (tys, ts), body) -> quant "forall" env fmt (tys, ts, body)
    | Binder (Letand l, body) -> letand env fmt (l, body)
    | Binder (Letin l, body) -> letin env fmt (l, body)

  and term_app env fmt (t_ty, head, args) =
    (* first, we need to undo any left/right associativity/chainability that
       may have been expanded by the typechecker or other mechanism. *)
    let head, args =
      let args =
        match term_cst_assoc env head with
        | `Left_assoc top_head -> E.left_assoc top_head args
        | `Right_assoc top_head -> E.right_assoc top_head args
        | `None -> args
      in
      match V.Term.Cst.builtin head, args with
      | B.And, t :: _ ->
        begin match V.Term.view t with
          | App (h, _, _) ->
            begin match term_cst_chainable env h with
              | `Chainable top_head ->
                begin match E.chainable top_head args with
                  | Some new_args -> h, new_args
                  | None -> head, args
                end
              | `Nope -> head, args
            end
          | _ -> head, args
        end
      | _ -> head, args
    in
    (* smtlib has implicit type arguments, i.e. the type args are not printed.
       Therefore, whenever a polymorphic symbol is used, its type arguments
       need to be inferable from its term arguments. Hence, when a symbol is
       polymorphic and there are no term arguments, we need to print an
       explicit type annotation to disambiguate things. In the other cases,
       we suppose that a symbol's type arguments can be deduced from the term
       arguments. *)
    let aux h args =
      match args with
      | [] ->
        if term_cst_poly env head then
          Format.fprintf fmt "(as@ %a@ %a)"
            (id ~allow_keyword:false env) h (ty env) t_ty
        else
          Format.fprintf fmt "%a" (id ~allow_keyword:false env) h
      | _ :: _ ->
        Format.fprintf fmt "(%a@ %a)" (id ~allow_keyword:false env) h (list term env) args
    in
    (* small shorthand *)
    let p ns name = aux (Dolmen_std.Id.create ns name) args in
    let simple s = p Term (N.simple s) in
    match V.Term.Cst.builtin head with
    (* Base + Algebraic datatypes *)
    | B.Base | B.Constructor _ | B.Destructor _ ->
      p Term (Env.Term_cst.name env head)
    | B.Tester { cstr; _ } ->
      begin match Env.Term_cst.name env cstr with
        | Simple s -> p Term (N.indexed "is" [s])
        | _ -> _cannot_print "expected a simple for a constructor name"
      end
    (* Boolean core *)
    | B.True -> simple "true"
    | B.False -> simple "false"
    | B.Neg -> simple "not"
    | B.And -> simple "and"
    | B.Or -> simple "or"
    | B.Xor -> simple "xor"
    | B.Imply -> simple "=>"
    | B.Ite -> simple "ite"
    | B.Equal -> simple "="
    | B.Distinct -> simple "distinct"
    (* TODO: complete support for all builtins *)
    | B.Integer s -> p (Value Integer) (N.simple s)
    | B.Add (`Int | `Real) -> simple "+"
    | _ -> _cannot_print "unknown term builtin"

  and letin env fmt (l, body) =
    match l with
    | [] -> term env fmt body
    | binding :: r ->
      let env' = add_binding_to_env env binding in
      Format.fprintf fmt "@[<hv>(let (%a)@ %a)@]"
        (var_binding env' env) binding (letin env') (r, body)

  and letand env fmt (l, body) =
    let env' = List.fold_left add_binding_to_env env l in
    Format.fprintf fmt "@[<hv>(let @[<hv>(%a)@]@ %a)@]"
      (list (var_binding env') env) l (term env) body

  and var_binding var_env t_env fmt (v, t) =
    Format.fprintf fmt "@[<hov 2>(%a@ %a)@]" (term_var var_env) v (term t_env) t

  and term_match env fmt (scrutinee, cases) =
    Format.fprintf fmt "@[<hv 2>(match@ @[<hov>%a@]@ (%a))"
      (term env) scrutinee
      (list match_case env) cases

  and match_case env fmt (pat, arm) =
    let env = add_pattern_to_env env pat in
    Format.fprintf fmt "(@[<h>%a@] @[<hov>%a@])" (pattern env) pat (term env) arm

  and pattern env fmt pat =
    match (pat : _ F.Term.pattern) with
    | Var v -> term_var env fmt v
    | Constructor (c, []) -> term_cst env fmt c
    | Constructor (c, args) ->
      Format.fprintf fmt "(%a %a)"
        (term_cst env) c (list term_var env) args

  and quant q env fmt (tys, ts, body) =
    (* TODO: patterns/triggers *)
    match tys, ts with
    | _ :: _, _ -> _cannot_print "type quantification"
    | [], [] -> term env fmt body
    | [], _ :: _ ->
      Format.fprintf fmt "(%s@ (%a)@ %a)" q
        (list sorted_var env) ts
        (term env) body

  and prop_literal env fmt t =
    (* either 'c' or 'not c' with 'c' a constant *)
    match V.Formula.view t with
    | App (f, [], [arg]) when (match V.Term.Cst.builtin f with B.Neg -> true | _ -> false) ->
      begin match V.Term.view arg with
        | App (c, [], []) ->
          let name = Env.Term_cst.name env c in
          Format.fprintf fmt "(not %a)" (symbol env) name
        | _ -> _cannot_print "not a prop literal"
      end
    | App (c, [], []) ->
      let name = Env.Term_cst.name env c in
      symbol env fmt name
    | _ -> _cannot_print "not a prop literal"

  and formula env fmt t =
    term_view env fmt (V.Formula.ty t) (V.Formula.view t)

  (* Datatypes *)
  (* ********* *)

  let constructor_dec env fmt (cstr, params) =
    match params with
    | [] ->
      Format.fprintf fmt "(%a)" (term_cst env) cstr
    | _ ->
      let aux env fmt (tty, dstr) =
        Format.fprintf fmt "@[<h>(%a %a)@]"
          (term_cst env) dstr (ty env) tty
      in
      Format.fprintf fmt "@[<hv 1>(%a@ %a)@]"
        (term_cst env) cstr
        (list aux env) params

  let datatype_dec env fmt (_, vars, cases) =
    match vars with
    | [] ->
      Format.fprintf fmt "@[<v 1>(%a)@]" (list constructor_dec env) cases
    | _ ->
      let env = List.fold_left Env.Ty_var.bind env vars in
      Format.fprintf fmt "(par (%a)@ @[<v 1>(%a))@]"
        (list ty_var env) vars (list constructor_dec env) cases


  (* Attributes *)
  (* ********** *)

  let rec sexpr env fmt t =
    match S.view t with
    | Symbol s -> id ~allow_keyword:true env fmt s
    | App l -> list sexpr env fmt l

  let is_keyword t =
    match S.view t with
    | Symbol { ns = Attr; name = Simple s; }
      when Misc.lex_string Lexer.check_keyword s -> true
    | _ -> false

  let attribute env fmt t =
    match S.view t with
    | App ([k; _]) when is_keyword k -> sexpr env fmt t
    | _ -> _cannot_print "not an attribtue"

  let keyword env fmt t =
    if is_keyword t
    then sexpr env fmt t
    else _cannot_print "not a keyword"


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
    Format.fprintf fmt "@[<h>(set-logic %a)@]" symbol_aux s

  let set_info env fmt t =
    Format.fprintf fmt "@[<h>(set-info %a)@]" (attribute env) t

  let set_option env fmt t =
    Format.fprintf fmt "@[<h>(set-option %a)@]" (attribute env) t

  let get_info env fmt t =
    Format.fprintf fmt "@[<h>(get-info %a)@]" (keyword env) t

  let get_option env fmt t =
    Format.fprintf fmt "@[<h>(get-option %a)@]" (keyword env) t

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
    Format.fprintf fmt "(declare-sort %a %d)" (symbol env) name n

  let declare_datatype env fmt ((c, _, _) as dec) =
    Format.fprintf fmt "@[<hov 2>(declare-datatype %a@ %a)@]"
      (ty_cst env) c
      (datatype_dec env) dec

  let declare_datatypes env fmt l =
    let sort_dec env fmt (c, _, _) =
      let n = V.Ty.Cst.arity c in
      Format.fprintf fmt "@[<h>(%a %d)@]" (ty_cst env) c n
    in
    match l with
    | [decl] -> declare_datatype env fmt decl
    | _ ->
      Format.fprintf fmt "@[<v 2>(declare-datatypes@ @[<v 1>(%a)@]@ (%a))@]"
        (list sort_dec env) l
        (list datatype_dec env) l

  let declare_fun env fmt c =
    let name = Env.Term_cst.name env c in
    let c_sig = V.Term.Cst.ty c in
    match V.Sig.view c_sig with
    | Signature ([], [], c_ty) ->
      Format.fprintf fmt "(declare-const %a %a)"
        (symbol env) name (ty env) c_ty
    | Signature ([], params, ret) ->
      Format.fprintf fmt "(declare-fun %a (%a) %a)"
        (symbol env) name (list ty env) params (ty env) ret
    | Signature (_ :: _, _, _) ->
      _cannot_print "polymorphic function declaration"

  let define_sort env fmt (c, params, body) =
    let env = List.fold_left Env.Ty_var.bind env params in
    Format.fprintf fmt "(define-sort %a (%a) %a)"
      (ty_cst env) c
      (list ty_var env) params
      (ty env) body

  let define_fun_aux ~recursive env fmt (f, params, body) =
    let env = List.fold_left Env.Term_var.bind env params in
    Format.fprintf fmt "@[<hv 2>(@[<hov 1>%s %a@ (%a) %a@]@ %a)@]"
      (if recursive then "define-fun-rec" else "define-fun")
      (term_cst env) f
      (list sorted_var env) params
      (ty env) (V.Term.ty body)
      (term env) body

  let define_fun = define_fun_aux ~recursive:false
  let define_fun_rec = define_fun_aux ~recursive:true

  let define_funs_rec env fmt l =
    let fun_body env fmt (_, _, body) = term env fmt body in
    let fun_decl env fmt (f, params, body) =
      let env = List.fold_left Env.Term_var.bind env params in
      Format.fprintf fmt "(%a (%a) %a)"
        (term_cst env) f
        (list sorted_var env) params
        (ty env) (V.Term.ty body)
    in
    Format.fprintf fmt
      "@[<v 2>(define-funs-rec@ @[<v 2>(%a)@]@ @[<v 2>(%a)@])@]"
      (list fun_decl env) l
      (list fun_body env) l

  let assert_ env fmt t =
    Format.fprintf fmt "@[<hov 2>(assert %a)@]" (formula env) t

  let check_sat_assuming env fmt = function
    | [] -> check_sat env fmt ()
    | _ :: _ as l ->
      Format.fprintf fmt "@[<hov >(check-sat-assuming (%a))"
        (list prop_literal env) l

end

