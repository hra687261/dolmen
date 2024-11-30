
module Id = Dolmen.Std.Id

(* Smtlib Unicode Strings *)
(* ************************************************************************ *)

module Smtlib2 = struct

  module Tff
      (Type : Tff_intf.S)
      (Ty : Dolmen.Intf.Ty.Smtlib_NSeq with type t := Type.Ty.t)
      (T : Dolmen.Intf.Term.Smtlib_NSeq with type t := Type.T.t
                                         and type ty := Type.Ty.t) = struct

    let parse _version env s =
      match s with
      | Type.Id { name = Simple "NSeq"; ns = Sort } ->
        Type.builtin_ty (Base.ty_app1 (module Type) env s Ty.nseq)
      | Type.Id { name = Simple "nseq.first"; ns = Term } ->
        Type.builtin_term (Base.term_app1 (module Type) env s T.NSeq.first)
      | Type.Id { name = Simple "nseq.last"; ns = Term } ->
        Type.builtin_term (Base.term_app1 (module Type) env s T.NSeq.last)
      | Type.Id { name = Simple "nseq.length"; ns = Term } ->
        Type.builtin_term (Base.term_app1 (module Type) env s T.NSeq.length)
      | Type.Id { name = Simple "nseq.get"; ns = Term } ->
        Type.builtin_term (Base.term_app2 (module Type) env s T.NSeq.get)
      | Type.Id { name = Simple "nseq.set"; ns = Term } ->
        Type.builtin_term (Base.term_app3 (module Type) env s T.NSeq.set)
      | Type.Id { name = Simple "nseq.const"; ns = Term } ->
        Type.builtin_term (Base.term_app3 (module Type) env s T.NSeq.const)
      | Type.Id { name = Simple "nseq.relocate"; ns = Term } ->
        Type.builtin_term (Base.term_app2 (module Type) env s T.NSeq.relocate)
      | Type.Id { name = Simple "nseq.concat"; ns = Term } ->
        Type.builtin_term (Base.term_app2 (module Type) env s T.NSeq.concat)
      | Type.Id { name = Simple "nseq.slice"; ns = Term } ->
        Type.builtin_term (Base.term_app3 (module Type) env s T.NSeq.slice)
      | Type.Id { name = Simple "nseq.update"; ns = Term } ->
        Type.builtin_term (Base.term_app2 (module Type) env s T.NSeq.update)
      | Type.Id { name = Simple "nseq.content"; ns = Term } ->
        Type.builtin_term (Base.term_app1 (module Type) env s T.NSeq.content)
      | _ -> `Not_found

  end

end
