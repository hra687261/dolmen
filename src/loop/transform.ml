
(* This file is free software, part of Dolmen. See file "LICENSE" for more details. *)

(* Statement transformation / normalisation

   This module defines a pipe to apply transformations to terms and statements
*)

(* Transforming errors *)
(* ************************************************************************ *)

type language = Logic.language

let code = Code.create
    ~category:"transform"
    ~descr:"on trasnformation errors"

let unsupported_language =
  Report.Error.mk ~code ~mnemonic:"transform-unsupported-lang"
    ~message:(fun fmt lang ->
        Format.fprintf fmt
          "The following format is not (yet) supported for transform: %s"
          (Logic.string_of_language lang)
      )
    ~name:"Unsupported Transform Language" ()

let non_minimal_logic =
  Report.Warning.mk ~code ~mnemonic:"non-minimal-logic"
    ~message:(fun fmt (old_logic, new_logic) ->
        Format.fprintf fmt
          "The logic used to typecheck the problem (%s) is not minimal. \
           The minimal logic actually is: %s" old_logic new_logic
      )
    ~name:"Non Minimal Logic" ()

let non_handled_builtin =
  Report.Error.mk ~code ~mnemonic:"transform-unhandled-builtin"
    ~message:(fun fmt (lang, f) ->
        let aux pp arg =
          Format.fprintf fmt "%a %s:@ %a"
            Format.pp_print_text
            "The following symbol cannot be exported in"
            lang pp arg
        in
        match f with
        | `Ty c -> aux Dolmen_std.Expr.Ty.Const.print c
        | `Term c -> aux Dolmen_std.Expr.Term.Const.print c)
    ~name:"Unhandled Builtin" ()


(* Common interface for transformation *)
(* ************************************************************************ *)

module Dummy = struct

  type acc = unit

  let transform st () l = st, (), l

end

(* Smtlib2 transformation *)
(* ************************************************************************ *)

module Smtlib2
    (State : State.S)
    (Typer_Types : Typer.Types
     with type ty = Dolmen_std.Expr.ty
      and type ty_var = Dolmen_std.Expr.ty_var
      and type ty_cst = Dolmen_std.Expr.ty_cst
      and type ty_def = Dolmen_std.Expr.ty_def
      and type term = Dolmen_std.Expr.term
      and type term_var = Dolmen_std.Expr.term_var
      and type term_cst = Dolmen_std.Expr.term_cst
      and type formula = Dolmen_std.Expr.term)
= struct

  let pipe = "Transform"

  module View = Dolmen_std.Expr.View.TFF
  module S = Dolmen_type.Logic.Smtlib2.Scan(View)

  type old_logic =
    | Not_seen_yet
    | Logic of (string * Typer_Types.typechecked Typer_Types.stmt) option

  type acc = {
    seen_exit : bool;
    scan_acc : S.acc option;
    old_logic : old_logic;
    pre_logic_stmts : Typer_Types.typechecked Typer_Types.stmt list;
    post_logic_stmts : Typer_Types.typechecked Typer_Types.stmt list;
  }

  let init ~compute_logic =
    {
      seen_exit = false;
      scan_acc = if compute_logic then Some S.nothing else None;
      old_logic = Not_seen_yet;
      pre_logic_stmts = [];
      post_logic_stmts = [];
    }

  let need_logic = function
    | Not_seen_yet -> Logic None
    | Logic _ as l -> l

  let compute_logic st acc =
    match acc.scan_acc with
    | None ->
      begin match acc.old_logic with
        | Not_seen_yet | Logic None -> st, []
        | Logic Some (_, stmt) -> st, [stmt]
      end
    | Some scan_acc ->
      let logic = S.to_logic scan_acc in
      let logic_name = Dolmen_type.Logic.Smtlib2.to_string logic in
      let st =
        match acc.old_logic with
        | Logic Some (old_logic, _stmt) when old_logic <> logic_name ->
          State.warn st non_minimal_logic (old_logic, logic_name)
        | _ -> st
      in
      (* TODO: expose a function to create stmts in Typer_Types *)
      let set_logic : Typer_Types.typechecked Typer_Types.stmt = {
        id = Dolmen.Std.Id.create Attr (Dolmen.Std.Name.simple "set_logic");
        loc = Dolmen.Std.Loc.no_loc;
        attrs = [];
        implicit = false;
        contents = `Set_logic (logic_name, Smtlib2 logic);
      } in
      (* Accumulate top-level declaration *)
      let acc = [] in
      (* Unit type *)
      let acc =
        if not (S.need_unit scan_acc) then acc
        else begin
          let cst = Dolmen.Std.Expr.Ty.Const.unit in
          let declare_unit : Typer_Types.typechecked Typer_Types.stmt = {
            id = Dolmen.Std.Id.create Attr (Dolmen.Std.Name.simple "declare_unit");
            loc = Dolmen.Std.Loc.no_loc;
            attrs = [];
            implicit = false;
            contents = `Decls (false, [`Type_decl (cst,
                                                   Dolmen.Std.Expr.Ty.definition cst
                                                  )]);
          } in
          declare_unit :: acc
        end
      in
      (* Univ/tptp's $i type *)
      let acc =
        if not (S.need_univ scan_acc) then acc
        else begin
          let declare_univ : Typer_Types.typechecked Typer_Types.stmt = {
            id = Dolmen.Std.Id.create Attr (Dolmen.Std.Name.simple "declare_univ");
            loc = Dolmen.Std.Loc.no_loc;
            contents = `Decls (false, [`Type_decl (Dolmen.Std.Expr.Ty.Const.base, None)]);
            attrs = [];
            implicit = false;
          } in
          declare_univ :: acc
        end
      in
      st, set_logic :: acc

  let flush st acc res =
    let st, logic_stmts = compute_logic st acc in
    let res =
      res @
      List.rev_append acc.pre_logic_stmts (
        logic_stmts @ List.rev acc.post_logic_stmts)
    in
    let acc = { acc with pre_logic_stmts = []; post_logic_stmts = []; } in
    st, acc, res

  (** Try and simplify some series of statements. Note that the list here is
      in reverse order (so the first element is the last statement seen). *)
  let reduce_post_logic_stmts = function
    (* fallback *)
    | l -> l

  let add_post_logic_stmt acc stmt =
    let post_logic_stmts = stmt :: acc.post_logic_stmts in
    let post_logic_stmts = reduce_post_logic_stmts post_logic_stmts in
    { acc with post_logic_stmts; }

  let add_pre_logic_stmt acc stmt =
    { acc with pre_logic_stmts = stmt :: acc.pre_logic_stmts; }

  let add_stmt acc stmt =
    match acc.old_logic with
    | Not_seen_yet -> add_pre_logic_stmt acc stmt
    | Logic _ -> add_post_logic_stmt acc stmt

  let accumulate_logic_aux (st, acc, res) (stmt : Typer_Types.typechecked Typer_Types.stmt) =
    match stmt.contents with
    (* Just record the old logic, if any *)
    | `Set_logic (s, _) ->
      begin match acc.old_logic with
        | Not_seen_yet ->
          let acc = { acc with old_logic = Logic (Some (s, stmt)); } in
          st, acc, res
        | Logic _ ->
          (* TODO: proper error *)
          assert false
      end
    (* Not much to do for these statements *)
    | #Typer_Types.get_info
    | #Typer_Types.set_info
    | `Push _ | `Pop _ | `Reset_assertions (* `Reset must be handled separately *)
      ->
      let acc = add_stmt acc stmt in
      st, acc, res

    (* Decls & Defs *)
    | `Defs (_, l) ->
      let old_logic = need_logic acc.old_logic in
      let scan_acc =
        Option.map (fun scan_acc ->
            List.fold_left (fun scan_acc def ->
                match def with
                | `Type_alias _ -> scan_acc
                | `Term_def (_, _, _, _, body) -> S.scan_term scan_acc body
                | `Instanceof(_, _, _, _, _, body) -> S.scan_term scan_acc body
                (* TODO: in the Instanceof case, we might want to look at the term_cst
                     being instantiated to update the scan accumulator. *)
              ) scan_acc l
          ) acc.scan_acc
      in
      let acc = { acc with old_logic; scan_acc; } in
      st, add_stmt acc stmt, res
    | `Decls (_, l) ->
      let old_logic = need_logic acc.old_logic in
      let scan_acc =
        Option.map (fun scan_acc ->
            List.fold_left (fun scan_acc decl ->
                match decl with
                | `Type_param_decl _ -> S.add_free_sort scan_acc
                | `Term_decl c -> S.scan_term_decl ~in_adt:false scan_acc c
                | `Type_decl (_, ty_def) ->
                  begin match (ty_def : Dolmen.Std.Expr.ty_def option) with
                    | None | Some Abstract -> S.add_free_sort scan_acc
                    | Some Adt { ty = _; record = _; cases; } ->
                      let scan_acc = S.add_datatypes scan_acc in
                      Array.fold_left (fun scan_acc (case : Dolmen.Std.Expr.ty_def_adt_case)->
                          S.scan_term_decl ~in_adt:true scan_acc case.cstr
                        ) scan_acc cases
                  end
              ) scan_acc l
          ) acc.scan_acc
      in
      let acc = { acc with old_logic; scan_acc; } in
      st, add_stmt acc stmt, res

    (* Hyps & Goals *)
    | `Hyp f | `Goal f ->
      let old_logic = need_logic acc.old_logic in
      let scan_acc = Option.map (fun scan_acc -> S.scan_term scan_acc f) acc.scan_acc in
      let acc = { acc with old_logic; scan_acc; } in
      st, add_stmt acc stmt, res
    | `Clause l ->
      let old_logic = need_logic acc.old_logic in
      let scan_acc = Option.map (fun scan_acc -> List.fold_left S.scan_term scan_acc l) acc.scan_acc in
      let acc = { acc with old_logic; scan_acc; } in
      st, add_stmt acc stmt, res
    | `Solve (hyps, goals) ->
      let old_logic = need_logic acc.old_logic in
      let scan_acc = Option.map (fun scan_acc -> List.fold_left S.scan_term scan_acc hyps) acc.scan_acc in
      let scan_acc = Option.map (fun scan_acc -> List.fold_left S.scan_term scan_acc goals) scan_acc in
      let acc = { acc with old_logic; scan_acc; } in
      st, add_stmt acc stmt, res

    (* Exit, Reset and End trigger a flush of the statements and logic computed. *)
    | `Exit ->
      let acc = add_stmt acc stmt in
      let st, acc, res = flush st acc res in
      let acc = { acc with seen_exit = true; } in
      st, acc, res
    | `Reset ->
      let acc = add_stmt acc stmt in
      flush st acc res
    | `End ->
      if acc.seen_exit then begin
        assert (acc.pre_logic_stmts = [] &&
                acc.post_logic_stmts = []);
        st, acc, [stmt]
      end else begin
        let acc =
          let exit : _ Typer_Types.stmt = {
            id = Dolmen.Std.Id.create Attr (Dolmen.Std.Name.simple "exit");
            loc = Dolmen.Std.Loc.no_loc;
            contents = `Exit;
            attrs = [];
            implicit = false;
          } in
          add_post_logic_stmt acc exit
        in
        let acc = add_post_logic_stmt acc stmt in
        flush st acc res
      end

  let accumulate_logic ((st, acc, res) as arg) stmt =
    try accumulate_logic_aux arg stmt
    with
    | S.Unknown_ty_builtin f ->
      let st = State.error st non_handled_builtin ("SMT-LIB", `Ty f) in
      (st, acc, res)
    | S.Unknown_term_builtin f ->
      let st = State.error st non_handled_builtin ("SMT-LIB", `Term f) in
      (st, acc, res)

  let transform st acc (l : Typer_Types.typechecked Typer_Types.stmt list) =
    List.fold_left accumulate_logic (st, acc, []) l

end

(* Seq2NSeq translation *)
(* ************************************************************************ *)

module Seq2NSeq
    (State : State.S)
    (Typer_Types : Typer.Types
     with type ty = Dolmen_std.Expr.ty
      and type ty_var = Dolmen_std.Expr.ty_var
      and type ty_cst = Dolmen_std.Expr.ty_cst
      and type ty_def = Dolmen_std.Expr.ty_def
      and type term = Dolmen_std.Expr.term
      and type term_var = Dolmen_std.Expr.term_var
      and type term_cst = Dolmen_std.Expr.term_cst
      and type formula = Dolmen_std.Expr.term)
= struct

  let pipe = "Transform"

  module View = Dolmen_std.Expr.View.TFF
  module S = Dolmen_type.Logic.Smtlib2.Scan(View)
  module Expr = Dolmen_std.Expr
  module Term = Expr.Term
  module Ty = Expr.Ty
  module Builtin = Dolmen_std.Builtin

  let a_tyv = Ty.Var.mk "A"
  let a_ty = Ty.of_var a_tyv
  let a_ns_ty = Ty.nseq a_ty

  let element_ty_cst = Ty.Const.mk (Dolmen_std.Path.global "Element") 0
  let element_ty = Ty.apply element_ty_cst []
  let element_ns_ty = Ty.nseq element_ty

  (* let nseq_empty_cst =
     Expr.Term.Const.mk (Dolmen_std.Path.local "nseq.empty") (a_ns_ty) *)

  let nseq_empty_cst_poly mono =
    Expr.Term.Const.mk (Dolmen_std.Path.local "nseq.empty")
      (if mono then element_ns_ty else Ty.pi [ a_tyv ] a_ns_ty)

  let nseq_empty_declaration mono:
    Typer_Types.typechecked Typer_Types.stmt list =
    let nseq_empty_decl = Typer_Types.{
        id = Dolmen_std.Id.mk Dolmen_std.Namespace.Term "nseq.empty";
        loc = Dolmen_std.Loc.no_loc;
        contents = `Decls (false, [`Term_decl (nseq_empty_cst_poly mono)]);
        attrs = [];
        implicit = false;
      }
    in
    if mono then (
      let element_ty_decl = Typer_Types.{
          id = Dolmen_std.Id.mk Dolmen_std.Namespace.Term "";
          loc = Dolmen_std.Loc.no_loc;
          contents = `Decls (false, [`Type_decl (element_ty_cst, None)]);
          attrs = [];
          implicit = false;
        }
      in
      (* unnecessary for qf benchs *)
      ignore (element_ty_decl, nseq_empty_decl);
      []
    ) else
      let a_ty_decl = Typer_Types.{
          id = Dolmen_std.Id.mk Dolmen_std.Namespace.Term "";
          loc = Dolmen_std.Loc.no_loc;
          contents = `Decls (false, [`Type_param_decl a_tyv]);
          attrs = [];
          implicit = false;
        }
      in
      [ a_ty_decl; nseq_empty_decl ]

  (*
     let first_cond = Typer_Types.{
        id = Dolmen_std.Id.mk Dolmen_std.Namespace.Term "";
        loc = Dolmen_std.Loc.no_loc;
        contents =
          `Hyp (Term.eq (Term.NSeq.first nseq_empty) (Term.Int.mk "0"));
        attrs = [];
        implicit = false;
      }
     in
     let last_cond = Typer_Types.{
        id = Dolmen_std.Id.mk Dolmen_std.Namespace.Term "";
        loc = Dolmen_std.Loc.no_loc;
        contents =
          `Hyp (Term.eq (Term.NSeq.last nseq_empty) (Term.Int.mk "-1"));
        attrs = [];
        implicit = false;
      }
     in
     [declaration; first_cond; last_cond] *)

  type acc = {
    monomorphize : bool;
    stmts_before_first_decls_and_asserts :
      Typer_Types.typechecked Typer_Types.stmt list;
    other_stmts :
      Typer_Types.typechecked Typer_Types.stmt list;
  }

  let init ~monomorphize () = {monomorphize; stmts_before_first_decls_and_asserts = []; other_stmts = []}

  let translate_binder (binder: Expr.binder): Expr.binder =
    binder

  let rec translate_ty (ty: Typer_Types.ty): Typer_Types.ty =
    match ty.Expr.ty_descr with
    | TyVar _ -> ty
    | TyApp ({builtin = Builtin.Seq; _ }, [v]) ->
      Ty.nseq v
    | TyApp (ty_cst, tyl) ->
      Ty.apply ty_cst (List.map translate_ty tyl)
    | Arrow (tyl, ty) ->
      Ty.arrow (List.map translate_ty tyl) (translate_ty ty)
    | Pi (tyvl, ty) ->
      Ty.pi tyvl (translate_ty ty)

  let cst_db = Hashtbl.create 17

  let translate_term_cst =
    fun (t: Expr.ty Expr.id) ->
    match t with
    (* | { id_ty
          { ty_descr = TyApp ({builtin = Builtin.Seq; _ }, [ _ ]); _ };
        builtin = Builtin.Seq_empty; _
       } -> nseq_empty_cst *)

    | { id_ty = {
        ty_descr = TyApp ({builtin = Builtin.Seq; _ }, [ _ ]); _
      }; _ } ->
      let id = Term.Const.hash t in
      (match Hashtbl.find_opt cst_db id with
       | None ->
         let newc = Term.Const.mk t.path (translate_ty t.id_ty) in
         Hashtbl.add cst_db id newc;
         newc
       | Some c ->
         c)
    | _ -> t

  let mk_concat =
    let rec aux prec l =
      match l with
      | [] -> prec
      | h :: t ->
        let next_fst = Term.Int.add (Term.NSeq.last prec) (Term.Int.mk "1") in
        let prec = Term.NSeq.concat prec (Term.NSeq.relocate h next_fst) in
        aux prec t
    in
    fun (l: View.term list): View.term ->
      match l with
      | [] | [_] -> assert false
      | h :: t -> aux h t

  let rec translate_term mono (term: View.term): View.term =
    let translate_term = translate_term mono in
    match term.term_descr with
    | Var v ->
      Term.of_var ((translate_term_cst v))

    | Cst cst ->
      Term.of_cst ((translate_term_cst cst))

    | App ({ term_descr = Cst {builtin = Builtin.Seq_empty; _ }; _ }, [ vty ], []) ->
      Term.apply_cst (nseq_empty_cst_poly mono) [ vty ] []

    | App (
        {term_descr = Cst {builtin = Builtin.Seq_unit; _}; _},
        [ _ ], [ v ]
      ) ->
      Term.NSeq.const (Term.Int.mk "0") (Term.Int.mk "0") (translate_term v)

    | App (
        {term_descr = Cst {builtin = Builtin.Seq_len; _}; _},
        [ _ ], [ s ]
      ) ->
      Term.Int.add (Term.NSeq.last (translate_term s)) (Term.Int.mk "1")

    | App (
        {term_descr = Cst {builtin = Builtin.Seq_nth; _}; _},
        [ _ ], [ s; i ]
      ) ->
      Term.NSeq.get (translate_term s) (translate_term i)

    | App (
        {term_descr = Cst {builtin = Builtin.Seq_concat; _}; _},
        [ _ ], l
      ) ->
      mk_concat (List.map translate_term l)

    | App (
        {term_descr = Cst {builtin = Builtin.Seq_update; _}; _},
        [ _ ],
        [ a; i; {
              term_descr = App (
                  {term_descr = Cst {builtin = Builtin.Seq_unit; _}; _},
                  [ _ ],
                  [ v ]); _
            }
        ]
      ) ->
      let a = translate_term a in
      let i = translate_term i in
      let v = translate_term v in
      Term.NSeq.set a i v

    | App (
        {term_descr = Cst {builtin = Builtin.Seq_update; _}; _},
        [ _ ], [ a; i; b ]
      ) ->
      let a = translate_term a in
      let i = translate_term i in
      let b = translate_term b in
      let lsta = Term.NSeq.last a in
      let lstb = Term.NSeq.last b in
      let c1 = Term._or [
          Term.Int.lt i (Term.Int.mk "0");
          Term.Int.gt i lsta ]
      in
      let c2 =
        Term.Int.gt (Term.Int.add i lstb) lsta
      in
      let relb = Term.NSeq.relocate b i in
      let slrelb = Term.NSeq.slice relb i lsta in
      Term.ite c1 a
        (Term.ite c2
           (Term.NSeq.update a slrelb)
           (Term.NSeq.update a relb))

    | App (
        {term_descr = Cst {builtin = Builtin.Seq_extract; _}; _},
        [ _ ], [ a; i; l ]
      ) ->
      let a = translate_term a in
      let i = translate_term i in
      let l = translate_term l in
      let lsta = Term.NSeq.last a in
      let c1 = Term._or [
          Term.Int.lt i (Term.Int.mk "0");
          Term.Int.gt i lsta;
          Term.Int.le l (Term.Int.mk "0")]
      in
      let lstls = Term.Int.sub (Term.Int.add i l) (Term.Int.mk "1") in
      let c2 = Term.Int.gt lstls lsta in
      Term.ite c1 a
        (Term.ite c2
           (Term.NSeq.slice a i lsta)
           (Term.NSeq.slice a i lstls))

    | App (app, tyl, l) ->
      Term.apply
        (translate_term app)
        (List.map translate_ty tyl)
        (List.map translate_term l)

    | Binder (Let_seq bindings, term) ->
      let bindings =
        List.map (fun (v,t) ->
            (translate_term_cst v, translate_term t)
          ) bindings
      in
      Term.letin bindings (translate_term term)

    | Binder (Let_par bindings, term) ->
      let bindings =
        List.map (fun (v,t) ->
            (translate_term_cst v, translate_term t)
          ) bindings
      in
      Term.letand bindings (translate_term term)

    | Binder (Lambda (tyvl, termvl), term) ->
      Term.lam
        (tyvl, List.map translate_term_cst termvl)
        (translate_term term)

    | Binder (Exists (tyvl, termvl), term) ->
      Term.ex
        (tyvl, List.map translate_term_cst termvl)
        (translate_term term)

    | Binder (Forall (tyvl, termvl), term) ->
      Term.all
        (tyvl, List.map translate_term_cst termvl)
        (translate_term term)

    | Match (term, patl) ->
      Term.pattern_match
        (translate_term term)
        (List.map (fun (p, t) ->
             (* Translating patterns should be unnecessary *)
             (translate_term p, translate_term t)
           ) patl)

  let translate_ty_def (ty_def: Typer_Types.ty_def): Typer_Types.ty_def =
    match ty_def with
    | Abstract -> ty_def
    | Adt {ty; record; cases} ->
      let cases =
        Array.map (fun Expr.{cstr; tester; dstrs} ->
            let dstrs = Array.map (Option.map translate_term_cst) dstrs in
            Expr.{cstr; tester; dstrs}
          ) cases
      in
      Adt {ty; record; cases}

  let translate_decl (d: Typer_Types.decl): Typer_Types.decl =
    match d with
    | `Type_param_decl _
    | `Type_decl (_, None) -> d
    | `Type_decl (ty, Some ty_def) -> `Type_decl (ty, Some (translate_ty_def ty_def))
    | `Term_decl tc -> `Term_decl (translate_term_cst tc)

  let translate_stmt (st, acc, res) (stmt : Typer_Types.typechecked Typer_Types.stmt) =
    let translate_term = translate_term acc.monomorphize in
    match stmt.contents with
    | `Decls (b, decl) -> (
        st,
        { acc with other_stmts = {
              stmt with
              contents = `Decls (b, List.map translate_decl decl)} :: acc.other_stmts },
        res
      )
    | `Defs (b, defl) ->
      let defl =
        List.fold_left (fun acc def ->
            match def with
            | `Type_alias _ -> def :: acc
            | `Term_def (id, tcst, tyvl, params, body) ->
              `Term_def (
                id, tcst, tyvl,
                List.map translate_term_cst params,
                translate_term body
              ) :: acc
            | `Instanceof (id, f, ty_args, vars, params, body) ->
              `Instanceof (
                id, f, ty_args, vars,
                List.map translate_term_cst params,
                translate_term body
              ) :: acc
          ) [] defl |> List.rev
      in
      (st,
       { acc with other_stmts = {
             stmt with
             contents = `Defs (b, defl)} :: acc.other_stmts },
       res)

    | `Hyp t -> (
        st,
        { acc with other_stmts = {
              stmt with
              contents = `Hyp (translate_term t)} :: acc.other_stmts },
        res
      )
    | `Goal t -> (
        st,
        { acc with other_stmts = {
              stmt with
              contents = `Goal (translate_term t)} :: acc.other_stmts },
        res
      )
    | `Clause l -> (
        st,
        { acc with other_stmts = {
              stmt with
              contents = `Clause (List.map translate_term l)} :: acc.other_stmts },
        res
      )
    | `Solve (hyps, goals) -> (
        st,
        { acc with other_stmts = {
              stmt with
              contents = `Solve (
                  List.map translate_term hyps,
                  List.map translate_term goals
                )
            } :: acc.other_stmts },
        res
      )
    | `Get_value l -> (
        st,
        { acc with other_stmts =
                     {stmt with
                      contents = `Get_value (List.map translate_term l)} :: acc.other_stmts },
        res
      )
    | `End ->
      st, {
        acc with
        stmts_before_first_decls_and_asserts = [];
        other_stmts = []
      },
      List.rev_append acc.stmts_before_first_decls_and_asserts @@
      nseq_empty_declaration acc.monomorphize @
      (List.rev_append acc.other_stmts res)

    | _ when acc.other_stmts = [] ->
      (st,
       { acc with
         stmts_before_first_decls_and_asserts =
           stmt :: acc.stmts_before_first_decls_and_asserts },
       res)

    | _ ->
      (st, { acc with other_stmts = stmt :: acc.other_stmts }, res)

  let transform st acc (l : Typer_Types.typechecked Typer_Types.stmt list) =
    List.fold_left translate_stmt (st, acc, []) l

end

(* Pipe functor *)
(* ************************************************************************ *)

module Make
    (State : State.S)
    (Typer_Types : Typer.Types
     with type ty = Dolmen.Std.Expr.ty
      and type ty_var = Dolmen.Std.Expr.ty_var
      and type ty_cst = Dolmen.Std.Expr.ty_cst
      and type ty_def = Dolmen.Std.Expr.ty_def
      and type term = Dolmen.Std.Expr.term
      and type term_var = Dolmen.Std.Expr.term_var
      and type term_cst = Dolmen.Std.Expr.term_cst
      and type formula = Dolmen.Std.Expr.term)
= struct


  (* Type definitions *)
  type stmt = Typer_Types.typechecked Typer_Types.stmt

  module type S = sig
    type acc
    val transform : State.t -> acc -> stmt list -> State.t * acc * stmt list
  end

  type 'acc transformer = (module S with type acc = 'acc)

  type state =
    | No_transform : state
    | Transform : {
        acc : 'acc;
        transformer : 'acc transformer;
      } -> state

  (* available transformers *)

  module Smt2 = Smtlib2(State)(Typer_Types)
  module Seq2NSeq = Seq2NSeq(State)(Typer_Types)

  (* setup *)

  let pipe = "Transform"

  let state : state State.key =
    State.create_key ~pipe "transform_state"

  let init ~compute_logic ~translate ~monomorphize ?lang st =
    let mk (type acc) (acc : acc) (transformer : acc transformer) =
      Transform { acc; transformer; }
    in
    let mk st lang =
      match (lang : language) with
      | Smtlib2 _ when translate ->
        st, mk (Seq2NSeq.init ~monomorphize ()) (module Seq2NSeq)
      | Smtlib2 _ ->
        let acc = mk (Smt2.init ~compute_logic) (module Smt2) in
        st,  acc
      | lang ->
        let st = State.error st unsupported_language lang in
        st, mk () (module Dummy)
    in
    let st, state_value =
      match lang with
      | Some lang ->
        mk st lang
      | None ->
        begin match State.get State.export_file st with
          | { lang = None; _ } -> st, No_transform
          | { lang = Some lang; _ } -> mk st lang
          | exception State.Key_not_found _ -> st, No_transform
        end
    in
    st
    |> State.set state state_value

  (* interface *)

  let transform st (l : Typer_Types.typechecked Typer_Types.stmt list) =
    match State.get state st with
    | No_transform -> st, l
    | Transform { acc; transformer; } ->
      let (module T) = transformer in
      let st, acc, l = T.transform st acc l in
      let st = State.set state (Transform { acc; transformer }) st in
      st, l

end
