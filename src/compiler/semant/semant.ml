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
  let rec trexp (A.Exp {exp_base; pos}) : TA.exp =
    match exp_base with
    | VarExp var -> (
        let tvar = trvar var in
        match tvar with
        | TA.Var {ty; _} -> TA.Exp {exp_base= VarExp tvar; pos; ty} )
    | A.NilExp -> TA.Exp {exp_base= TA.NilExp; pos; ty= Ty.NIL}
    | A.IntExp i -> TA.Exp {exp_base= TA.IntExp i; pos; ty= Ty.INT}
    | A.StringExp s -> TA.Exp {exp_base= TA.StringExp s; pos; ty= Ty.STRING}
    | A.CallExp {func; args} -> (
      (* Lookup the function in the variable environment *)
      match S.look (venv, func) with
      | None ->
          Err.error err pos (EFmt.errorFunctionUndefined func) ;
          err_exp pos
      | Some tFunc -> call_exp func tFunc args pos )
    | OpExp {left; oper; right} ->
        let t_left = check_type (trexp left) INT EFmt.errorArith in
        let t_right = check_type (trexp right) INT EFmt.errorArith in
        TA.Exp
          { exp_base= TA.OpExp {left= t_left; oper; right= t_right}
          ; pos
          ; ty= INT }
    (* | RecordExp {fields; typ} -> (
       match S.look (tenv, typ) with
       | None -> ( Err.error err pos (EFmt.errorTypeDoesNotExist typ) ;
                   err_exp pos )
       | Some type_rec ->
          match actual_type err pos type_rec with
          | RECORD (fields = t_fileds; _) ->
          | _ -> raise NotImplemented ) *)
    | IfExp {test; thn; els} -> if_exp test thn els pos
    | _ -> raise NotImplemented
  (* Compute an error expression. *)
  and err_exp pos = TA.Exp {exp_base= TA.ErrorExp; pos; ty= Ty.ERROR}
  and check_type t_exp expected_t err_type =
    match t_exp with
    | TA.Exp {ty; pos; _} ->
        if ty = expected_t then t_exp
        else (
          Err.error err pos err_type ;
          err_exp pos )
  (* Helper function for call expression. *)
  and call_exp func tFunc args pos =
    (* Match the types of the function. *)
    match tFunc with
    | FunEntry {formals; result} ->
        if List.length args != List.length formals then (
          Err.error err pos (EFmt.errorFunctionArguments func) ;
          err_exp pos )
        else
          (* Check if arguments have correct type *)
          let typeCheckArgs = List.map (fun x -> trexp x) args in
          let argTypes =
            List.map
              (fun x -> match x with TA.Exp {ty; _} -> ty)
              typeCheckArgs
          in
          (* Check types of arguments are the same as specified for function. *)
          if List.equal (fun x y -> x == y) argTypes formals then
            TA.Exp
              { exp_base= TA.CallExp {func; args= typeCheckArgs}
              ; pos
              ; ty= result }
          else (
            (* Arguments did not match specified types. *)
            Err.error err pos (EFmt.errorFunctionArguments func)
            (* This should probably be another error... *) ;
            err_exp pos )
    | _ ->
        Err.error err pos (EFmt.errorUsingVariableAsFunction func) ;
        err_exp pos
  and if_exp test thn els pos =
    (* Type check test and then. *)
    let (TA.Exp {ty= testTy; _} as evalTest) = trexp test in
    let (TA.Exp {ty= thnTy; _} as evalThn) = trexp thn in
    (* Check test *)
    if testTy == Ty.INT then
      (* Test is INT. *)
      (* Check if there exists an else statement. *)
      match els with
      | None ->
          if (* No else statement. *)
             thnTy == Ty.VOID then
            (* Correct thn-body type. *)
            TA.Exp
              { exp_base= TA.IfExp {test= evalTest; thn= evalThn; els= None}
              ; pos
              ; ty= thnTy }
          else (
            (* Thn-body is not void. *)
            Err.error err pos (EFmt.errorIfThenShouldBeVoid thnTy) ;
            err_exp pos )
      | Some elseSt ->
          (* With else statement. *)
          let (TA.Exp {ty= elsTy; _} as evalEls) = trexp elseSt in
          if thnTy == elsTy then
            (* Same return type for then and else. *)
            TA.Exp
              { exp_base=
                  TA.IfExp {test= evalTest; thn= evalThn; els= Some evalEls}
              ; pos
              ; ty= elsTy }
          else (
            (* Not same return type for then and else. *)
            Err.error err pos (EFmt.errorIfBranchesNotSameType thnTy elsTy) ;
            err_exp pos )
    else (
      (* Test is not INT. *)
      Err.error err pos (EFmt.errorIntRequired testTy) ;
      err_exp pos )
  and trvar (A.Var {var_base; pos}) : TA.var =
    match var_base with
    (* Simple var i.e. `x` *)
    | A.SimpleVar s -> (
      match S.look (venv, s) with
      (* Look up the symbol s in venv *)
      | None ->
          (* Error, it does not exists *)
          Err.error err pos (EFmt.errorVariableUndefined s) ;
          TA.Var {var_base= TA.SimpleVar s; pos; ty= Ty.ERROR}
      | Some ent -> (
        match ent with
        | VarEntry ty -> TA.Var {var_base= TA.SimpleVar s; pos; ty}
        | FunEntry _ ->
            (*  *)
            Err.error err pos (EFmt.errorUsingFunctionAsVariable s) ;
            TA.Var {var_base= TA.SimpleVar s; pos; ty= Ty.ERROR} ) )
    (* FieldVar, i.e. `record.field` *)
    | A.FieldVar (v, s) -> (
        (* Type check the base variable v *)
        let (TA.Var {pos= p; ty= tpe; _} as tv) = trvar v in
        match actual_type err p tpe with
        | RECORD (fields, _) -> (
          (* Check that symbol s exists in record fields *)
          match List.assoc_opt s fields with
          | Some t -> TA.Var {var_base= TA.FieldVar (tv, s); pos; ty= t}
          | None ->
              Err.error err p (EFmt.errorRecordNonExistingField s tpe) ;
              TA.Var {var_base= TA.FieldVar (tv, s); pos; ty= Ty.ERROR} )
        | t ->
            (* Actual type of the variable v was not a record *)
            Err.error err pos (EFmt.errorRecordType t) ;
            TA.Var {var_base= TA.FieldVar (tv, s); pos; ty= Ty.ERROR} )
    (* SubscriptVar i.e. `arr[i]` *)
    | A.SubscriptVar (v, e) -> (
        (* Type check the base variable v *)
        let (TA.Var {pos= p; ty= tpe; _} as tv) = trvar v in
        let (TA.Exp {pos= ep; ty= etyp; _} as texp) = trexp e in
        (* Check that the actualy type is an array *)
        match (actual_type err p tpe, etyp) with
        | ARRAY (t, _), INT ->
            TA.Var {var_base= TA.SubscriptVar (tv, texp); pos; ty= t}
        | t, INT ->
            (* Error, actual type of var was not an array *)
            Err.error err p (EFmt.errorArrayType t) ;
            TA.Var {var_base= TA.SubscriptVar (tv, texp); pos; ty= Ty.ERROR}
        | ARRAY (_, _), et ->
            (* Error, actual type of exp was not an int *)
            Err.error err ep (EFmt.errorIntRequired et) ;
            TA.Var {var_base= TA.SubscriptVar (tv, texp); pos; ty= Ty.ERROR}
        | t, et ->
            (* Error, actual type of var was not array and actual type of exp was not int (combination of both) *)
            Err.error err p (EFmt.errorArrayType t) ;
            Err.error err ep (EFmt.errorIntRequired et) ;
            TA.Var {var_base= TA.SubscriptVar (tv, texp); pos; ty= Ty.ERROR}
        )
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
