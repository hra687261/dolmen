
(* This file is free software, part of dolmen. See file "LICENSE" formore information *)

(** iCNF language input *)

module type Term = Ast_iCNF.Term
module type Statement = Ast_iCNF.Statement
(** Implementation requirement for the iCNF format. *)

module Make
    (L : ParseLocation.S)
    (T : Term with type location := L.t)
    (S : Statement with type location := L.t and type term := T.t) :
  Language_intf.S with type statement = S.t
(** Functor to generate a parser for the iCNF format. *)
