(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(**************************************************************************)
open Tigercommon
module S = Symbol
module A = Absyn
module E = Semenv
module Err = Errenv
module EFmt = ErrorFormatter
module Ty = Types
module PT = Prtypes
module TA = Tabsyn

(** Context record contains the environments we use in our translation *)

type context =
  { venv: E.enventry S.table (* Γ from our formal typing rules *)
  ; tenv: Ty.ty S.table (* Δ from our formal typing rules *)
  ; err: Err.errenv (* error environment *) }

exception NotImplemented
(* the final code should work without this exception *)

open Ty

let rec transExp ({err; venv; tenv} : context) e =
  let rec trexp (A.Exp {exp_base; pos}) = raise NotImplemented
  and trvar (A.Var {var_base; _}) = raise NotImplemented in
  trexp e

and transDecl ({err; venv; tenv} : context) dec = raise NotImplemented

(* no need to change the implementation of the top level function *)

let transProg (e : A.exp) : TA.exp * Err.errenv =
  let err = Err.initial_env in
  (transExp {venv= E.baseVenv; tenv= E.baseTenv; err} e, err)
