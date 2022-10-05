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
  ; break: bool (* β from our formal typing rules *)
  ; err: Err.errenv (* error environment *) }

exception NotImplemented
(* the final code should work without this exception *)

open Ty

let rec transExp ({err; venv; tenv; break} : context) e =
  let rec trexp (A.Exp {exp_base; pos}) : TA.exp =
    match exp_base with
    | A.IntExp i -> TA.Exp {exp_base= TA.IntExp i; pos; ty= Ty.INT}
    | A.StringExp s -> TA.Exp {exp_base= TA.StringExp s; pos; ty= Ty.STRING}
    | A.NilExp -> TA.Exp {exp_base= TA.NilExp; pos; ty= Ty.NIL}
    | A.SeqExp [] -> TA.Exp {exp_base= TA.SeqExp []; pos; ty= Ty.VOID}
    | VarExp var -> (
        let tvar = trvar var in
        match tvar with
        | TA.Var {ty; _} -> TA.Exp {exp_base= VarExp tvar; pos; ty} )
    | A.CallExp {func; args} -> (
      (* Lookup the function in the variable environment *)
      match S.look (venv, func) with
      | None ->
          Err.error err pos (EFmt.errorFunctionUndefined func) ;
          err_exp pos
      | Some tFunc -> call_exp func tFunc args pos )
    | A.OpExp {left; oper; right} ->
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
       | Some type_rec -> (
          match actual_type err pos type_rec with
          | RECORD (fields = t_fields; _) -> (
            if List.length fields != List.length t_fields then (
              Err.error err pos EFmt.errorRecordFields
              err_exp pos
            ) else
              List.map (fun ff -> match ff with
                | ((name_given, val_given), (name_expec, val_ty_expec)) ->
                  if name_given != name_expec then (
                    Err.error err pos (EFmt.errorRecordFieldName name_given name_expec)
                    err_exp pos
                  ) else (

                  )
              ) List.combind fields t_fields
            (* let (field_names_given, field_vals_given) = List.split fields in
            let (field_names_expec, field_vals_expec) = List.split t_fields in *)

          )
          | _ -> raise NotImplemented
       )) *)
    | A.IfExp {test; thn; els} -> if_exp test thn els pos
    | A.WhileExp {test; body} -> (
        let (TA.Exp {ty= testTy; _} as t_test) = trexp test in
        let (TA.Exp {ty= bodyTy; _} as t_body) =
          transExp {err; venv; tenv; break= true} body
        in
        match (testTy, bodyTy) with
        | Ty.INT, Ty.VOID ->
            TA.Exp
              { exp_base= TA.WhileExp {test= t_test; body= t_body}
              ; pos
              ; ty= bodyTy }
            (* ---------- TODO : break = true ----------- *)
        | Ty.INT, _ ->
            Err.error err pos (EFmt.errorWhileShouldBeVoid bodyTy) ;
            err_exp pos
        | _ ->
            Err.error err pos (EFmt.errorIntRequired testTy) ;
            err_exp pos )
    | ForExp {var; escape; lo; hi; body} -> (
          let (TA.Exp {ty = loTy ; _} as t_lo) = trexp lo in
          let (TA.Exp {ty = hiTy ; _} as t_hi) = trexp hi in
          match (loTy, hiTy) with
          | (Ty.INT, Ty.INT) -> (
            let (TA.Exp {ty=bodyTy;_} as t_body) = transExp {err; venv = (S.enter (venv, var, (E.VarEntry Ty.INT))) ; tenv; break= true} body in
            raise NotImplemented
          )
          | (Ty.INT, _     ) -> Err.error err pos (EFmt.errorIntRequired hiTy); err_exp pos
          | _                -> Err.error err pos (EFmt.errorIntRequired loTy); err_exp pos
      )
    | A.BreakExp ->
        if break then TA.Exp {exp_base= BreakExp; pos; ty= Ty.VOID}
        else (
          Err.error err pos EFmt.errorBreak ;
          err_exp pos )
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
    let (TA.Exp {ty= testTy; _} as t_test) = trexp test in
    let (TA.Exp {ty= thnTy; _} as t_thn) = trexp thn in
    (* Check for else. *)
    match els with
    | None -> (
      match (testTy, thnTy) with
      | Ty.INT, Ty.VOID ->
          TA.Exp
            { exp_base= TA.IfExp {test= t_test; thn= t_thn; els= None}
            ; pos
            ; ty= thnTy }
      | Ty.INT, _ ->
          Err.error err pos (EFmt.errorIfThenShouldBeVoid thnTy) ;
          err_exp pos
      | _ ->
          Err.error err pos (EFmt.errorIntRequired testTy) ;
          err_exp pos )
    | Some elsSt -> (
        let (TA.Exp {ty= elsTy; _} as t_els) = trexp elsSt in
        match (testTy, thnTy, elsTy) with
        | Ty.INT, t1, t2 when t1 = t2 ->
            TA.Exp
              { exp_base= TA.IfExp {test= t_test; thn= t_els; els= Some t_els}
              ; pos
              ; ty= elsTy }
        | Ty.INT, _, _ ->
            Err.error err pos (EFmt.errorIfBranchesNotSameType thnTy elsTy) ;
            err_exp pos
        | _ ->
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

and transDecl ({err; venv; tenv; break} as ctx : context) dec =
  match dec with
  | A.VarDec {name; escape; typ= None; init; pos} -> (
      let (TA.Exp {pos= p; ty= etyp; _} as texp) = transExp ctx init in
      match etyp with
      | Ty.NIL ->
          Err.error err p EFmt.errorInferNilType ;
          (TA.VarDec {name; escape; typ= Ty.ERROR; init= texp; pos}, ctx)
      | Ty.VOID ->
          Err.error err p EFmt.errorVoid ;
          (TA.VarDec {name; escape; typ= Ty.ERROR; init= texp; pos}, ctx)
      | t ->
          ( TA.VarDec {name; escape; typ= t; init= texp; pos}
          , {err; venv= S.enter (venv, name, E.VarEntry t); tenv; break} ) )
  | _ -> raise NotImplemented

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
  (transExp {venv= E.baseVenv; tenv= E.baseTenv; err; break= false} e, err)
