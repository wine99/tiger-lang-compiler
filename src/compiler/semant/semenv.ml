(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(**************************************************************************)

open Tigercommon
module S = Symbol
module Ty = Types

type enventry =
  | VarEntry of {assignable: bool; ty: Types.ty}
  | FunEntry of {formals: (Types.ty option) list; result: Types.ty}

let add k v t = S.enter (t, k, v)

let baseVenv =
  S.empty
  |> add (S.symbol "print") (FunEntry {formals= [Some Ty.STRING]; result= Ty.VOID})
  |> add (S.symbol "flush") (FunEntry {formals= []; result= Ty.VOID})
  |> add (S.symbol "getchar") (FunEntry {formals= []; result= Ty.STRING})
  |> add (S.symbol "ord") (FunEntry {formals= [Some Ty.STRING]; result= Ty.INT})
  |> add (S.symbol "chr") (FunEntry {formals= [Some Ty.INT]; result= Ty.STRING})
  |> add (S.symbol "size") (FunEntry {formals= [Some Ty.STRING]; result= Ty.INT})
  |> add (S.symbol "substring")
       (FunEntry {formals= [Some Ty.STRING; Some Ty.INT; Some Ty.INT]; result= Ty.STRING})
  |> add (S.symbol "concat")
       (FunEntry {formals= [Some Ty.STRING; Some Ty.STRING]; result= Ty.STRING})
  |> add (S.symbol "not") (FunEntry {formals= [Some Ty.INT]; result= Ty.INT})
  |> add (S.symbol "exit") (FunEntry {formals= [Some Ty.INT]; result= Ty.VOID})

let baseTenv =
  S.empty |> add (S.symbol "int") Ty.INT |> add (S.symbol "string") Ty.STRING
