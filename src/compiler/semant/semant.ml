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

open Oper
let arithOps = [PlusOp; MinusOp; TimesOp; DivideOp; ExponentOp]
let compOps = [LtOp; LeOp; GtOp; GeOp]

let rec transExp ({err; venv; tenv; break} as ctx : context) e =
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
    | A.OpExp {left; oper; right} when List.exists (fun op -> op = oper) arithOps ->
        let t_left = check_type (trexp left) INT EFmt.errorArith in
        let t_right = check_type (trexp right) INT EFmt.errorArith in
        TA.Exp
          { exp_base= TA.OpExp {left= t_left; oper; right= t_right}
          ; pos
          ; ty= INT }
    | A.OpExp {left; oper; right} when List.exists (fun op -> op = oper) compOps -> (
        let (Exp {ty= ty_left; _} as t_left) = trexp left in
        let (Exp {ty= ty_right; _} as t_right) = trexp right in
        match ty_left , ty_right with
        | INT, INT | STRING, STRING ->
            TA.Exp
              { exp_base= TA.OpExp {left= t_left; oper; right= t_right}
              ; pos
              ; ty= INT }
        | _ ->
            Err.error err pos (EFmt.errorOtherComparison ty_left ty_right) ;
            err_exp pos
    )
    | A.OpExp {left; oper; right} ->
        let (Exp {ty= ty_left; pos= pos_left; _} as t_left) = trexp left in
        let (Exp {ty= ty_right; pos= pos_right; _} as t_right) = trexp right in
        if (are_comparable err ty_left pos_left ty_right pos_right
            || ty_left != NIL || ty_right != NIL)
        then
          TA.Exp
            { exp_base= TA.OpExp {left= t_left; oper; right= t_right}
            ; pos
            ; ty= INT }
        else (
          Err.error err pos (EFmt.errorOtherComparison ty_left ty_right) ;
          err_exp pos
        )
    | ArrayExp {size= size_exp; init= init_exp; typ} -> (
      match S.look (tenv, typ) with
      | None ->
          Err.error err pos (EFmt.errorTypeDoesNotExist typ) ;
          err_exp pos
      | Some type_arr -> (
        match actual_type err pos type_arr with
        | ARRAY (ty, _) -> (
            let (Exp {ty= ty_size; pos= pos_size; _} as t_size_exp) = trexp size_exp in
            let (Exp {ty= ty_init; pos= pos_init; _} as t_init_exp) = trexp init_exp in
            match ty_size , ty_init with
            | INT , _ when ty_init = ty ->
                TA.Exp
                  { exp_base= TA.ArrayExp {size= t_size_exp; init=t_init_exp}
                  ; pos
                  ; ty= type_arr }
            | INT , _ ->
                Err.error err pos_init (EFmt.errorArrayInitType ty_init ty) ;
                err_exp pos
            | _ ->
                Err.error err pos_size (EFmt.errorIntRequired ty_size) ;
                err_exp pos
        )
        | _ ->
          Err.error err pos (EFmt.errorArrayType type_arr) ;
          err_exp pos ) )
    | RecordExp {fields= fields_given; typ} -> (
      match S.look (tenv, typ) with
      | None ->
          Err.error err pos (EFmt.errorTypeDoesNotExist typ) ;
          err_exp pos
      | Some type_rec -> (
        match actual_type err pos type_rec with
        | RECORD (fields , _) ->
            let fields_expec = fields in
            if List.length fields_given != List.length fields_expec then (
              Err.error err pos EFmt.errorRecordFields ;
              err_exp pos )
            else
              let t_fields =
                List.map
                  (fun ff ->
                    match ff with
                    | (name_given, val_given), (name_expec, val_ty_expec) ->
                        if name_given != name_expec then (
                          Err.error err pos
                            (EFmt.errorRecordFieldName name_given name_expec) ;
                          (name_given, err_exp pos) )
                        else
                          let (TA.Exp {ty; _} as t_val) = trexp val_given in
                          if ty != val_ty_expec then (
                            Err.error err pos
                              (EFmt.errorRecordFieldType name_given val_ty_expec ty ) ;
                            (name_given, err_exp pos) )
                          else (name_given, t_val) )
                  (List.combine fields_given fields_expec)
              in
              TA.Exp
                {exp_base= TA.RecordExp {fields= t_fields}; pos; ty = type_rec}
        | _ ->
            Err.error err pos (EFmt.errorRecordType type_rec) ;
            err_exp pos ) )
    | SeqExp exps -> (
      let rec t_exp = function
        | [] -> [], Ty.VOID
        | [exp] -> (
          let (TA.Exp {ty ; _} as t_exp) = trexp exp in
          [t_exp], ty
        )
        | exp :: exps -> (
          let (t_exps, ty) = t_exp exps in
          trexp exp :: t_exps, ty
        )
      in
      let (t_exps, ty) = t_exp exps in
      TA.Exp { exp_base = TA.SeqExp t_exps ; pos ; ty}
    )
    | AssignExp {var; exp} -> (
      let (TA.Var {var_base ; ty = varTy; _} as t_var) = trvar var in
      let (Exp {ty = expTy ; _} as t_exp) = trexp exp in
      if varTy == expTy && assignable_var var_base then (
        TA.Exp {exp_base = TA.AssignExp {var = t_var ; exp = t_exp}; pos ; ty = varTy}
      ) else (
        Err.error err pos (EFmt.errorCoercible varTy expTy); (*Not sure if correct err_msg*)
        err_exp pos
      )
    )
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
            let (TA.Exp {ty=bodyTy;_} as t_body) = transExp {err; venv = (S.enter (venv, var, (E.VarEntry {assignable = false ; ty = Ty.INT}))) ; tenv; break= true} body in
            if bodyTy == Ty.VOID then
              TA.Exp { exp_base = ForExp { var ; escape ; lo = t_lo ; hi = t_hi ; body = t_body } ; pos ; ty = bodyTy }
            else (
              Err.error err pos (EFmt.errorForShouldBeVoid bodyTy);
              err_exp pos
            )
          )
          | (Ty.INT, _     ) -> Err.error err pos (EFmt.errorIntRequired hiTy); err_exp pos
          | _                -> Err.error err pos (EFmt.errorIntRequired loTy); err_exp pos
      )
    | A.BreakExp ->
        if break then TA.Exp {exp_base= BreakExp; pos; ty= Ty.VOID}
        else (
          Err.error err pos EFmt.errorBreak ;
          err_exp pos )
    | A.LetExp {decls ; body} -> ( (*Is LetEmpty not just a part of this?*)
      let t_decl_func acc decl = (
        let (t_decls, ctx0) = acc in
        let (t_decl, ctx1) = transDecl ctx0 decl in
        (t_decl :: t_decls, ctx1)
      ) in
      let (t_decls, ctx_new) = (List.fold_left (t_decl_func) ([], ctx) decls) in
      let (TA.Exp {ty ; _} as t_body) = transExp ctx_new body in
      TA.Exp { exp_base = TA.LetExp {decls = t_decls ; body = t_body} ; pos ; ty }
    )
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
  and assignable_var var = (
    match var with
    | TA.SimpleVar s -> (
      match S.look (venv, s) with
      | Some E.VarEntry {assignable ; _} -> assignable
      | _ -> false
    )
    | _ -> false
  )
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
        | VarEntry {ty; _} -> TA.Var {var_base= TA.SimpleVar s; pos; ty}
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
          , {err; venv= S.enter (venv, name, E.VarEntry {assignable = true; ty = t}); tenv; break} ) )
  | _ -> raise NotImplemented

and actual_type err pos = function
  | NAME (sym, opt_ty_ref) -> (
    match !opt_ty_ref with
    | None ->
        Err.error err pos (EFmt.errorTypeDoesNotExist sym) ;
        Ty.ERROR
    | Some a -> actual_type err pos a )
  | t -> t

and is_subtype err t1 pos1 t2 pos2 =
match (actual_type err pos1 t1, actual_type err pos2 t2) with
| (Ty.NIL, Ty.RECORD _) -> true
| _ -> t1 == t2

and are_comparable err t1 pos1 t2 pos2 =
t1 != Ty.VOID && ((is_subtype err t1 pos1 t2 pos2) || (is_subtype err t2 pos2 t1 pos1))

(* no need to change the implementation of the top level function *)

let transProg (e : A.exp) : TA.exp * Err.errenv =
  let err = Err.initial_env in
  (transExp {venv= E.baseVenv; tenv= E.baseTenv; err; break= false} e, err)
