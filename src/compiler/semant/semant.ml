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
  let rec trexp (A.Exp {exp_base; pos}) : Tabsyn.exp =
    let err_exp = TA.Exp {exp_base= TA.ErrorExp; pos; ty= Ty.ERROR} in
    match exp_base with
    | VarExp var -> (
        let tvar = trvar var in
        match tvar with
        | TA.Var {ty; _} -> TA.Exp {exp_base= VarExp tvar; pos; ty} )
    | A.NilExp -> TA.Exp {exp_base= TA.NilExp; pos; ty= Ty.NIL}
    | A.IntExp i -> TA.Exp {exp_base= TA.IntExp i; pos; ty= Ty.INT}
    | A.StringExp s -> TA.Exp {exp_base= TA.StringExp s; pos; ty= Ty.STRING}
    | A.CallExp {func; args} -> (
      match S.look (venv, func) with
      | None ->
          Err.error err pos (EFmt.errorFunctionUndefined func) ;
          err_exp
      | Some tFunc -> (
        match tFunc with
        | FunEntry {formals; result} ->
            if List.length args != List.length formals then (
              Err.error err pos (EFmt.errorFunctionArguments func) ;
              err_exp )
            else
              (* Check if arguments have correct type *)
              let argTy =
                List.map
                  (fun x -> match trexp x with TA.Exp {ty; _} -> ty)
                  args
              in
              if List.equal (fun x y -> x == y) argTy formals then
                raise NotImplemented
                (*TA.Exp { exp_base = TA.CallExp { func ; args } ; pos ; ty = result }*)
              else raise NotImplemented
        | _ ->
            Err.error err pos (EFmt.errorUsingVariableAsFunction func) ;
            err_exp ) )
    | _ -> raise NotImplemented
  and trvar (A.Var {var_base; pos}) : TA.var =
    match var_base with
    | A.SimpleVar s -> (
      match S.look (venv, s) with
      | None ->
          Err.error err pos (EFmt.errorVariableUndefined s) ;
          TA.Var {var_base= TA.SimpleVar s; pos; ty= Ty.ERROR}
      | Some ent -> (
        match ent with
        | VarEntry ty -> TA.Var {var_base= TA.SimpleVar s; pos; ty}
        | FunEntry _ ->
            Err.error err pos (EFmt.errorUsingFunctionAsVariable s) ;
            TA.Var {var_base= TA.SimpleVar s; pos; ty= Ty.ERROR} ) )
    | A.FieldVar (v, s) -> (
        let (Var {var_base; pos; ty}) = trvar v in
        match actual_type err pos ty with
        | RECORD (types, unique) -> raise NotImplemented
        | t ->
            Err.error err pos (EFmt.errorRecordType t) ;
            TA.Var
              { var_base= TA.FieldVar (Var {var_base; pos; ty}, s)
              ; pos
              ; ty= Ty.ERROR } )
    | A.SubscriptVar (v, e) -> raise NotImplemented
  in
  trexp e

and transDecl ({err; venv; tenv} : context) dec = raise NotImplemented

and actual_type err pos = function
  | NAME (sym, opt_ty_ref) -> (
    match !opt_ty_ref with
    | None ->
        Err.error err pos (EFmt.errorTypeDoesNotExist sym) ;
        Ty.ERROR
    | Some a -> actual_type err pos a )
  | t -> t

(* no need to change the implementation of the top level function *)

let transProg (e : A.exp) : TA.exp * Err.errenv =
  let err = Err.initial_env in
  (transExp {venv= E.baseVenv; tenv= E.baseTenv; err} e, err)
