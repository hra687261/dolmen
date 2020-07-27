(* This file is free software, part of Dolmen. See file "LICENSE" for more details. *)

(* The Main Dolmen library is used to parse input languages *)
(* ************************************************************************ *)

module P = Dolmen.Class.Logic.Make
    (Dolmen.Std.Loc)
    (Dolmen.Std.Id)
    (Dolmen.Std.Term)
    (Dolmen.Std.Statement)

include (P : Dolmen.Class.Logic.S with type statement := Dolmen.Std.Statement.t)

