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
        let t_left = trexp left in
        let t_right = trexp right in
        (* raise errorArith if not int *)
        (* match t_left with
           |
           check_type t_left INT EFmt.errorArith ;
           check_type t_right INT EFmt.errorArith ; *)
        TA.Exp
          { exp_base= TA.OpExp {left= t_left; oper; right= t_right}
          ; pos
          ; ty= INT }
    (* | RecordExp {field; typ} ->
       match S.look (tenv, typ) with
       | None -> Err.error err pos (EFmt.errorTypeDoesNotExist)
                 err_exp pos
       | Some typ ->
    *)
    | IfExp {test; thn; els} -> raise NotImplemented
    | _ -> raise NotImplemented
  (* Compute an error expression. *)
  and err_exp pos = TA.Exp {exp_base= TA.ErrorExp; pos; ty= Ty.ERROR}
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
        let (TA.Var {var_base= vb; pos= p; ty= tpe}) = trvar v in
        match actual_type err p tpe with
        | RECORD (fields, _) -> (
          (* Check that symbol s exists in record fields *)
          match List.assoc_opt s fields with
          | Some t ->
              TA.Var
                { var_base=
                    TA.FieldVar (TA.Var {var_base= vb; pos= p; ty= tpe}, s)
                ; pos
                ; ty= t }
          | None ->
              Err.error err p (EFmt.errorRecordNonExistingField s tpe) ;
              TA.Var
                { var_base=
                    TA.FieldVar (TA.Var {var_base= vb; pos= p; ty= tpe}, s)
                ; pos
                ; ty= Ty.ERROR } )
        | t ->
            (* Actual type of the variable v was not a record *)
            Err.error err pos (EFmt.errorRecordType t) ;
            TA.Var
              { var_base=
                  TA.FieldVar (TA.Var {var_base= vb; pos= p; ty= tpe}, s)
              ; pos
              ; ty= Ty.ERROR } )
    (* SubscriptVar i.e. `arr[i]` *)
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
