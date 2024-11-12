

(** Smtlib sequence builtins *)
module Smtlib2 : sig

  module Tff
      (Type : Tff_intf.S)
      (Ty : Dolmen.Intf.Ty.Smtlib_Seq with type t := Type.Ty.t)
      (T : Dolmen.Intf.Term.Smtlib_Seq with type t := Type.T.t
                                        and type ty := Type.Ty.t) : sig

    val parse : Dolmen.Smtlib2.version -> Type.builtin_symbols

  end

end
