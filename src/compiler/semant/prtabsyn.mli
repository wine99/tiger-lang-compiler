(**************************************************************************)
(* AU Compilation. Assignment submissions must not modify this file       *)
(**************************************************************************)

(** Typed AST pretty printer interface *)
open Tigercommon

val string_of_exp : int -> Tabsyn.exp -> string

val print_exp : int -> Format.formatter -> Tabsyn.exp -> unit
