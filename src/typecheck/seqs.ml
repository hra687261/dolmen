
module Id = Dolmen.Std.Id

(* Smtlib Sequences *)
(* ************************************************************************ *)

module Smtlib2 = struct

  module Tff
      (Type : Tff_intf.S)
      (Ty : Dolmen.Intf.Ty.Smtlib_Seq with type t := Type.Ty.t)
      (T : Dolmen.Intf.Term.Smtlib_Seq with type t := Type.T.t
                                        and type ty := Type.Ty.t) = struct

    let parse _version env s =
      match s with
      | Type.Id { name = Simple "Seq"; ns = Sort } ->
        Type.builtin_ty (Base.ty_app1 (module Type) env s Ty.seq)
      | Type.Id { name = Simple "seq.empty"; ns = Term } ->
        Type.builtin_term (fun ast args ->
            let index_ty =
              Type.wildcard env (Added_type_argument ast) Any_in_scope
            in
            Base.make_op0 (module Type) env s
              (fun _ _ -> T.Seq.empty index_ty) ast args
          )
      | Type.Id { name = Simple "seq.unit"; ns = Term } ->
        Type.builtin_term (Base.term_app1 (module Type) env s T.Seq.unit)
      | Type.Id { name = Simple "seq.len"; ns = Term } ->
        Type.builtin_term (Base.term_app1 (module Type) env s T.Seq.len)
      | Type.Id { name = Simple "seq.nth"; ns = Term } ->
        Type.builtin_term (Base.term_app2 (module Type) env s T.Seq.nth)
      | Type.Id { name = Simple "seq.update"; ns = Term } ->
        Type.builtin_term (Base.term_app3 (module Type) env s T.Seq.update)
      | Type.Id { name = Simple "seq.extract"; ns = Term } ->
        Type.builtin_term (Base.term_app3 (module Type) env s T.Seq.extract)
      | Type.Id { name = Simple "seq.++"; ns = Term } ->
        Type.builtin_term (Base.term_app_list (module Type) env s T.Seq.concat)
      | _ -> `Not_found

  end

end
