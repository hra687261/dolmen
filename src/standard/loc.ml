
(* This file is free software, part of dolmen. See file "LICENSE" for more information *)


(* Modules and aliases *)
(* ************************************************************************* *)

module type S = Dolmen_intf.Location.S

(* Type definitions *)
(* ************************************************************************* *)

(* Compact representation of locs. This is split into a very
   compact handcrafted representation, and some file meta-data.
   Compact locations record the start byte number from the beginning
   of the file + a byte length for the location span.
   The file meta-data record at which byte number each line of the file
   starts. *)
type file = {
  name : string;
  mutable table : int Vec.t;
}

(* A compact file location has to hold 2 unsigned integers, in as compact
   a form as possible. This leads to 2 representations used:
   - an int: the two ints are packed, each in half the bits of the int
   - if the ints to hold do not fit into half a caml int, then we fallback
     to a caml block holding the ints separately. In this case, some care
     is taken to be able to hold big enough ints even on a 32-bit platform *)
type t = Obj.t (* = int [@unboxed] | Extended of extended *)

(* The block types used when parts of a compact location
   cannot fit in one caml int. *)
type extended = {
  offset : int;
  length : int;
}

(* Convenient alias to store a compact location and file info *)
type full = {
  file : file;
  loc : t;
}

(* A full location (very much not compact) *)
type loc = {
  file : string;
  start_line : int;
  start_column : int;
  stop_line : int;
  stop_column : int;
}


exception Uncaught of t * exn
exception Lexing_error of t * string
exception Syntax_error of t * string
(** Exceptions that may occur during parsing *)

(* Compact locations *)
(* ************************************************************************* *)

let compact_part_size = Sys.int_size / 2
let compact_part_mask = -1 lsr (Sys.int_size - compact_part_size)

let split_compact (c : t) =
  if Obj.is_int c then begin
    let i : int = Obj.magic c in
    let offset = i land compact_part_mask in
    let length = (i lsr compact_part_size) land compact_part_mask in
    offset, length
  end else begin
    let e : extended = Obj.magic c in
    e.offset, e.length
  end

let mk_compact offset length =
  if 0 <= offset && offset <= compact_part_mask &&
     0 <= length && length <= compact_part_mask then begin
    let i = offset + length lsl compact_part_size in
    (Obj.magic i : t)
  end else begin
    let e = { offset; length; } in
    (Obj.magic e : t)
  end

(* File table *)
(* ************************************************************************* *)

let tables = Hashtbl.create 5

let file_name { name; _ } = name

let mk_file name =
  try Hashtbl.find tables name
  with Not_found ->
    let table = Vec.create () in
    let () = Vec.push table 0 in
    let file = { name; table; } in
    Hashtbl.add tables name file;
    file

let new_line file offset =
  assert (Vec.last file.table < offset);
  Vec.push file.table (offset - 1)

let newline filename =
  let file = mk_file filename in
  (fun lexbuf ->
     Lexing.new_line lexbuf;
     let offset = Lexing.lexeme_end lexbuf in
     new_line file offset)

let find_line file offset =
  let rec aux vec offset start stop =
    (* end condition *)
    if start >= stop then start else begin
      assert (start < stop);
      let m = (start + stop) / 2 in
      let o = Vec.get vec m in
      if o < offset then begin
        aux vec offset (m + 1) stop
      end else begin
        aux vec offset start m
      end
    end
  in
  let line = aux file.table offset 0 (Vec.size file.table) in
  let line_offset = Vec.get file.table (line - 1) in
  line_offset, line


(* Full locations *)
(* ************************************************************************* *)

let eq a b = a = b
let hash a = Hashtbl.hash a

(* Constructor functions *)
let mk file start_line start_column stop_line stop_column =
  { file; start_line; start_column; stop_line; stop_column; }

let no_loc = mk_compact 0 0

let mk_pos start stop =
  let open Lexing in
  let start_offset = start.pos_cnum in
  let stop_offset = stop.pos_cnum in
  let length = stop_offset - start_offset in
  mk_compact start_offset length

(* location from a lexbuf *)
let of_lexbuf lexbuf =
  let start = Lexing.lexeme_start_p lexbuf in
  let stop = Lexing.lexeme_end_p lexbuf in
  mk_pos start stop

(* Compact<->full translations *)
(* ************************************************************************* *)

let loc file c =
  let start_offset, length = split_compact c in
  let stop_offset = start_offset + length in
  let start_line_offset, start_line = find_line file start_offset in
  let start_column = start_offset - start_line_offset - 1 in
  let stop_line_offset, stop_line = find_line file stop_offset in
  let stop_column = stop_offset - stop_line_offset - 1 in
  mk file.name start_line start_column stop_line stop_column

let full_loc { file; loc = l; } = loc file l

let compact (t : loc) =
  let file = mk_file t.file in
  let start_line_offset = Vec.get file.table t.start_line in
  let start_offset = start_line_offset + t.start_column + 1 in
  let stop_line_offset = Vec.get file.table t.stop_line in
  let stop_offset = stop_line_offset + t.stop_column + 1 in
  let length = stop_offset - start_offset in
  file, mk_compact start_offset length


(* Printing and lexbuf handling *)
(* ************************************************************************* *)

let pp buf pos =
  if pos.start_line = pos.stop_line then
    if pos.start_column = pos.stop_column then
      Printf.bprintf buf "File \"%s\", <location missing>" pos.file
    else
      Printf.bprintf buf "File \"%s\", line %d, character %d-%d"
        pos.file pos.start_line pos.start_column pos.stop_column
  else
    Printf.bprintf buf "File \"%s\", line %d, character %d to line %d, character %d"
      pos.file
      pos.start_line pos.start_column
      pos.stop_line pos.stop_column

let fmt fmt pos =
  if pos.start_line = pos.stop_line then
    if pos.start_column = pos.stop_column then
      Format.fprintf fmt "File \"%s\", <location missing>" pos.file
    else
      Format.fprintf fmt "File \"%s\", line %d, character %d-%d"
        pos.file pos.start_line pos.start_column pos.stop_column
  else
    Format.fprintf fmt "File \"%s\", line %d, character %d to line %d, character %d"
      pos.file
      pos.start_line pos.start_column
      pos.stop_line pos.stop_column

let fmt_hint fmt pos =
  if pos.start_line = pos.stop_line then
    Format.fprintf fmt "%s%s"
      (String.make (pos.start_column) ' ')
      (String.make (pos.stop_column - pos.start_column) '^')

let fmt_pos fmt pos =
  if pos.start_line = pos.stop_line then
    if pos.start_column = pos.stop_column then
      Format.fprintf fmt "<location missing>"
    else
      Format.fprintf fmt "line %d, character %d-%d"
        pos.start_line pos.start_column pos.stop_column
  else
    Format.fprintf fmt "line %d, character %d to line %d, character %d"
      pos.start_line pos.start_column
      pos.stop_line pos.stop_column

