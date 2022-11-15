(**************************************************************************)
(* AU compilation.                                                        *)
(* Skeleton file -- expected to be modified as part of the assignment     *)
(**************************************************************************)

open Tigercommon
open Tigerhoist
module H = Habsyn
module Ty = Types
module S = Symbol
module B = Cfgbuilder
open Pp_habsyn

module SymbolMap = Map.Make (struct
  type t = S.symbol

  let compare = compare
end)

module UniqueMap = Map.Make (struct
  type t = Ty.unique

  let compare = compare
end)

type unique_env = Ll.tid UniqueMap.t

type fdecl_summary =
  { parent_opt: Ll.gid option (* optional symbol 'parent' in locals.parent *)
  ; locals_uid: Ll.uid (* symbol 'locals' in locals.field *)
  ; locals_tid: Ll.tid
        (* type of the struct of 'locals'. Each 'locals' struct is a distinct type *)
  ; offset_of_symbol: S.symbol -> int
        (* the offset of the symbol in 'locals', used for gep instruction *)
  }

type summary_env = fdecl_summary SymbolMap.t

exception NotImplemented

exception CodeGenerationBug

let ty_of_exp = function H.Exp {ty; _} -> ty

let rec sym_of_var = function
  | H.Var {var_base= AccessVar (_, s); _} -> s
  | H.Var {var_base= FieldVar (v, _); _} -> sym_of_var v
  | H.Var {var_base= SubscriptVar (v, _); _} -> sym_of_var v

let string_literal_llty str =
  let len = String.length str in
  Ll.Struct [Ll.I64; Ll.Array (len, Ll.I8)]

let string_literal_llstr str =
  let len = String.length str in
  Ll.GStruct [(Ll.I64, Ll.GInt len); (Ll.Array (len, Ll.I8), Ll.GString str)]

let rec ty_to_llty = function
  | Ty.INT -> Ll.I64
  | Ty.NIL -> Ll.Ptr I8
  | Ty.STRING -> Ll.Ptr I8
  | Ty.RECORD (ts, _) -> Ll.Struct (List.map mk_actual_llvm_type ts)
  | Ty.ARRAY _ -> Ll.Ptr I8
  | Ty.NAME (sym, _) -> Ll.Namedt sym
  | Ty.VOID -> Ll.Void
  | Ty.ERROR -> raise CodeGenerationBug

(** Returns the llvm type corresponding to the given type except for arrays
    and records which will be mappen to i8 pointers *)
and mk_actual_llvm_type = function
  | _, Ty.RECORD _ -> Ll.Ptr I8
  | _, Ty.ARRAY _ -> Ll.Ptr I8
  | _, t -> ty_to_llty t

type context =
  { break_lbl: Ll.lbl option
  ; summary: fdecl_summary
  ; uenv: unique_env
  ; senv: summary_env
  ; gdecls: (Ll.gid * Ll.gdecl) list ref }

(* Obs: this is a rather tricky piece of code; 2019-10-12 *)
let cg_tydecl (uenv : unique_env ref) (H.Tdecl {name; ty; _}) =
  let llvm_type = ty_to_llty ty in
  match ty with
  | Ty.INT -> Some (name, llvm_type) (* type a = int *)
  | Ty.STRING -> Some (name, llvm_type) (* type a = string *)
  | Ty.NAME (_, _) -> Some (name, llvm_type) (* type a = b *)
  | Ty.VOID -> Some (name, llvm_type)
  | Ty.RECORD (_, u) -> (
    match UniqueMap.find_opt u !uenv with
    | None ->
        uenv := UniqueMap.add u name !uenv ;
        Some (name, llvm_type)
    | Some _ -> None )
  | Ty.ARRAY (_, u) -> (
    match UniqueMap.find_opt u !uenv with
    | None ->
        uenv := UniqueMap.add u name !uenv ;
        Some (name, llvm_type)
    | Some _ -> None )
  | Ty.NIL -> None
  | Ty.ERROR -> None

let fresh =
  let open Freshsymbols in
  let env = empty in
  gensym env

let ptr_i8 = Ll.Ptr Ll.I8

let ( <$> ) f g x = f (g x)

let id = Fun.id

let ( $> ) b1 b2 = b2 <$> b1 (* buildlet composition *)

let ( @> ) (b, op) k = b $> k op

let ty_of_exp (H.Exp {ty; _}) = ty

let ty_of_var (H.Var {ty; _}) = ty

let ty_of_arg (H.Arg {ty; _}) = ty

let name_of_arg (H.Arg {name; _}) = name

let default_sl_name = S.symbol "$sl"

let locals_type_name name = S.symbol @@ "$locals_" ^ S.name name

let ty_dec_name name = S.symbol @@ "t_$" ^ S.name name

(* add instruction with fresh symbol *)
let aiwf s i =
  let t = fresh s in
  (B.add_insn (Some t, i), Ll.Id t)

let biwf t i = (B.add_insn (Some t, i), Ll.Id t)
(* --- monadic interface;) ----------------------------- *)

(* Notes on the monadic interface:

   1) Monadic interface is not necessary at all, and one could just
      program with buildlets as before; it's just a little bit more
      concise, but one _really_ needs to know what they are doing.

   2) Some useful info on the OCmal let* notation here
      http://jobjo.github.io/2019/04/24/ocaml-has-some-new-shiny-syntax.html

   3) Observe that the new OCaml notation conflicts with JaneStreet
      pre-processors, so we don't have any pre-processing in this library.
*)

type 'a m = B.buildlet * 'a

let bind ((builder, op) : 'a m) (f : 'a -> 'b m) : 'b m =
  let builder', op' = f op in
  (builder $> builder', op')

let return x = (B.id_buildlet, x)

let ( let* ) = bind
(* --- end of monadic interface ------------------------ *)

let unit b = (b, ())

let build_store t o1 o2 = B.add_insn (None, Ll.Store (t, o1, o2))

let gep_0 ty op i = Ll.Gep (ty, op, [Const 0; Const i])

let ar_oper =
  [Oper.PlusOp; Oper.MinusOp; Oper.TimesOp; Oper.DivideOp; Oper.ExponentOp]

let cmp_oper =
  [Oper.EqOp; Oper.NeqOp; Oper.LtOp; Oper.LeOp; Oper.GtOp; Oper.GeOp]

let rec cgExp ctxt (Exp {exp_base; ty; _} as exp : H.exp) :
    B.buildlet * Ll.operand (* Alternatively: Ll.operand m *) =
  let cgE_ = cgExp ctxt in
  match exp_base with
  | IntExp i -> (id, Const i)
  (*| H.OpExp {left; right; oper; _} ->
      let build_right, op_right = cgE_ right in
      let build_left, op_left = cgE_ left in
      let bop =
        match oper with
        | PlusOp -> Ll.Add
        | MinusOp -> Ll.Sub
        | TimesOp -> Ll.Mul
        | _ -> raise NotImplemented
      in
      let i = Ll.Binop (bop, Ll.I64, op_left, op_right) in
      let newid = fresh "temp" in
      let builder = Cfgbuilder.add_insn (Some newid, i) in
      let builder' =
        Cfgbuilder.seq_buildlets [build_left; build_right; builder]
      in
      (builder', Ll.Id newid)
      (* the above can be rewritten using the monadic interface and aux functions
         as follows *)
  *)
  | H.OpExp {left; right; oper; _}
    when List.exists (fun x -> x = oper) ar_oper ->
      let* op_left = cgE_ left in
      let* op_right = cgE_ right in
      let bop =
        match oper with
        | PlusOp -> Ll.Add
        | MinusOp -> Ll.Sub
        | TimesOp -> Ll.Mul
        | DivideOp -> Ll.SDiv
        | ExponentOp -> raise NotImplemented
        | _ -> raise NotImplemented
      in
      let i = Ll.Binop (bop, Ll.I64, op_left, op_right) in
      aiwf "arith_tmp" i
  | H.OpExp {left; right; oper; _}
    when List.exists (fun x -> x = oper) cmp_oper -> (
      (* TODO special case comparison of string *)
      let* op_left = cgE_ left in
      let* op_right = cgE_ right in
      let cnd =
        match oper with
        | EqOp -> Ll.Eq
        | NeqOp -> Ll.Ne
        | LtOp -> Ll.Slt
        | LeOp -> Ll.Sle
        | GtOp -> Ll.Sgt
        | GeOp -> Ll.Sge
        | _ -> raise NotImplemented
      in
      match left with
      | H.Exp {ty; _} ->
          let* tmp =
            aiwf "cmp_tmp" @@ Ll.Icmp (cnd, ty_to_llty ty, op_left, op_right)
          in
          aiwf "cmp_tmp" @@ Ll.Zext (Ll.I1, tmp, Ll.I64) )
  | H.AssignExp {var; exp} ->
      let* e = cgE_ exp in
      let* dest = cgVar ctxt var in
      let t = ty_to_llty @@ ty_of_exp exp in
      let store = Ll.Store (t, e, dest) in
      (B.add_insn (None, store), Ll.Null)
  | H.LetExp {vardecl; body} -> (
    match vardecl with
    | VarDec {name; typ; init; _} ->
        let* e = cgE_ init in
        let* dest =
          cgParentLookup ctxt ctxt.summary (Ll.Id ctxt.summary.locals_uid)
            name 0
        in
        let store = Ll.Store (ty_to_llty typ, e, dest) in
        let* _ = (B.add_insn (None, store), Ll.Null) in
        cgE_ body )
  | H.SeqExp exps ->
      let rec loop exps =
        match exps with
        | [] -> (B.id_buildlet, Ll.Null)
        | [e] -> cgE_ e
        | e :: es ->
            let* _ = cgE_ e in
            loop es
      in
      loop exps
  | H.VarExp (H.Var {ty; _} as var) ->
      let* var_ptr = cgVar ctxt var in
      let load = Ll.Load (ty_to_llty ty, var_ptr) in
      aiwf "var_tmp" load
  | H.IfExp {test; thn; els= Some els} ->
      let res = fresh "local_ifs" in
      let res_ty = ty_to_llty ty in
      let thn_lbl = fresh "then" in
      let els_lbl = fresh "else" in
      let merge_lbl = fresh "merge" in
      let* res_ptr = (B.add_alloca (res, res_ty), Ll.Id res) in
      let* test_res_i64 = cgE_ test in
      let* test_res =
        aiwf "test_res" @@ Ll.Icmp (Ll.Eq, Ll.I64, test_res_i64, Ll.Const 1)
      in
      let* _ =
        (B.term_block (Ll.Cbr (test_res, thn_lbl, els_lbl)), Ll.Null)
      in
      let* _ = (B.start_block thn_lbl, Ll.Null) in
      let* thn_op = cgE_ thn in
      let* _ = (build_store res_ty thn_op res_ptr, Ll.Null) in
      let* _ = (B.term_block (Ll.Br merge_lbl), Ll.Null) in
      let* _ = (B.start_block els_lbl, Ll.Null) in
      let* els_op = cgE_ els in
      let* _ = (build_store res_ty els_op res_ptr, Ll.Null) in
      let* _ = (B.term_block (Ll.Br merge_lbl), Ll.Null) in
      let* _ = (B.start_block merge_lbl, Ll.Null) in
      aiwf "if_res" @@ Ll.Load (res_ty, res_ptr)
  | H.IfExp {test; thn; els= None} ->
      let thn_lbl = fresh "then" in
      let merge_lbl = fresh "merge" in
      let* test_res_i64 = cgE_ test in
      let* test_res =
        aiwf "test_res" @@ Ll.Icmp (Ll.Eq, Ll.I64, test_res_i64, Ll.Const 1)
      in
      let* _ =
        (B.term_block (Ll.Cbr (test_res, thn_lbl, merge_lbl)), Ll.Null)
      in
      let* _ = (B.start_block thn_lbl, Ll.Null) in
      let* _ = cgE_ thn in
      let* _ = (B.term_block (Ll.Br merge_lbl), Ll.Null) in
      (B.start_block merge_lbl, Ll.Null)
  | H.StringExp str ->
      let str_id = fresh "string_lit" in
      let str_ty = string_literal_llty str in
      let ll_str = string_literal_llstr str in
      ctxt.gdecls := (str_id, (str_ty, ll_str)) :: !(ctxt.gdecls) ;
      aiwf "string" @@ Ll.Bitcast (Ll.Ptr str_ty, Ll.Gid str_id, ptr_i8)
  | H.CallExp {func; lvl_diff; args} ->
      let rec loop args =
        match args with
        | [] -> (id, [])
        | a :: args -> (
            let build, op = cgE_ a in
            match loop args with builds, ops -> (build $> builds, op :: ops)
            )
      in
      let build, ops = loop args in
      (* find the right static link using ctxt and lvl_diff *)
      raise NotImplemented
  | H.WhileExp {test; body} ->
      let test_lbl = fresh "test" in
      let body_lbl = fresh "body" in
      let merge_lbl = fresh "merge" in
      (* Test block *)
      let* _ = (B.start_block test_lbl, Ll.Null) in
      let* test_res_i64 = cgE_ test in
      let* test_res =
        aiwf "test_res" @@ Ll.Icmp (Ll.Eq, Ll.I64, test_res_i64, Ll.Const 1)
      in
      let* _ =
        (B.term_block (Ll.Cbr (test_res, body_lbl, merge_lbl)), Ll.Null)
      in
      (* Body block *)
      let* _ = (B.start_block body_lbl, Ll.Null) in
      let* _ = cgExp {ctxt with break_lbl= Some merge_lbl} body in
      let* _ = (B.term_block (Ll.Br test_lbl), Ll.Null) in
      (* Merge block *)
      (B.start_block merge_lbl, Ll.Null)
  | H.BreakExp -> (
    match ctxt.break_lbl with
    | None -> raise NotImplemented
    | Some merge_lbl -> (B.term_block (Ll.Br merge_lbl), Ll.Null) )
  | _ ->
      Pp_habsyn.pp_exp exp Format.std_formatter () ;
      raise NotImplemented

and cgVar (ctxt : context) (H.Var {var_base; pos; ty}) =
  let llvm_type = ty_to_llty ty in
  match var_base with
  | AccessVar (i, sym) ->
      let op = Ll.Id ctxt.summary.locals_uid in
      cgParentLookup ctxt ctxt.summary op sym i
  | FieldVar (var, sym) -> raise NotImplemented
  | SubscriptVar (v, exp) ->
      let* cg_var = cgVar ctxt v in
      let* cg_exp = cgExp ctxt exp in
      raise NotImplemented
  | _ -> raise NotImplemented

(* TODO: Remove if cgParentLookup is succesful / correct
   and cgParentL (ctxt : context) fdecl_summary i sym =
     let rec loop oper sumry n =
       let locals_tpe = Ll.Namedt sumry.locals_tid in
       match n with
       | 0 ->
           let offset = sumry.offset_of_symbol sym in
           let load_locals_inst = gep_0 locals_tpe oper offset in
           aiwf (S.name sym ^ "_ptr") load_locals_inst
       | _ -> (
           let psym =
             match sumry.parent_opt with
             | None -> raise CodeGenerationBug
             | Some s -> s
           in
           let offset = sumry.offset_of_symbol psym in
           let gep_parent = gep_0 locals_tpe oper offset in
           let* inst = aiwf (S.name psym ^ "_ptr") gep_parent in
           let psumry = SymbolMap.find_opt psym ctxt.senv in
           match psumry with
           | None -> raise CodeGenerationBug
           | Some pfs -> loop inst pfs (n - 1) )
     in
     let op = Ll.Id fdecl_summary.locals_uid in
     loop op fdecl_summary i
*)

(* TODO change the function name to cgVarLookup *)
and cgParentLookup (ctxt : context) (summary : fdecl_summary) parent_ptr sym
    = function
  | 0 ->
      aiwf
        (S.name sym ^ "_ptr")
        (gep_0 (Namedt summary.locals_tid) parent_ptr
           (summary.offset_of_symbol sym) )
  | n ->
      let parent_sym =
        match summary.parent_opt with
        | Some sym -> sym
        | None -> raise CodeGenerationBug
      in
      let parent_summary = SymbolMap.find parent_sym ctxt.senv in
      let* parent_parent_ptr =
        aiwf
          (S.name parent_sym ^ "_ptr")
          (gep_0 (Namedt summary.locals_tid) parent_ptr 0)
      in
      cgParentLookup ctxt parent_summary parent_parent_ptr sym (n - 1)

(* --- From this point on the code requires no changes --- *)

(* Creates summary of a function declaration; relies on the alpha conversion *)
let cg_fdecl_summary senv_ref (H.Fdecl {name; parent_opt; locals; _}) =
  let locals_uid = fresh "locals" in
  let locals_tid = locals_type_name name in
  let offset_of_symbol =
    let locals_map =
      default_sl_name :: List.map fst locals
      |> List.mapi (fun i x -> (x, i))
      |> List.to_seq |> SymbolMap.of_seq
    in
    fun sym -> SymbolMap.find sym locals_map
  in
  senv_ref :=
    SymbolMap.add name
      {parent_opt; locals_uid; locals_tid; offset_of_symbol}
      !senv_ref ;
  let sl_type =
    match parent_opt with
    | Some p -> Ll.Ptr (Ll.Namedt (p |> locals_type_name))
    | None -> Ll.Ptr I8
  in
  let locals_ty =
    Ll.Struct (sl_type :: List.map (fun (_, t) -> ty_to_llty t) locals)
  in
  (locals_tid, locals_ty)

(* --- Code genartion of function bodies --- *)
let cg_fdecl senv uenv gdecls (H.Fdecl {name; args; result; body; _}) =
  (* Function bodies are generated in 5 steps
     1. Creating the translation context
     2. Allocating the locals structure with all the variables
     3. Copying the arguments to the locals
     4. Generating the code for the function body
     5. Terminate the function

     Because we use buildlets, the order in which we take steps 2-4 does not
     matter as long as we compose the resulting buildlets correctly in the
     end.
  *)
  let open Ll in
  (* locally open the Ll module; for convenience *)

  (* Extract the necessary information from the function summary environment *)
  let ({parent_opt; locals_uid; locals_tid; offset_of_symbol; _} as summary)
      =
    SymbolMap.find name senv
  in
  (* Get the name of the static link
     - either from the lookup in the summary, if the function is not main
     - a dummy i8*, for the main function
  *)
  let sl_type =
    match parent_opt with
    | Some p -> Ll.Ptr (Ll.Namedt (SymbolMap.find p senv).locals_tid)
    | None -> Ll.Ptr I8
  in
  (* A tuple that contains all sl-related information  *)
  let sl_info = (default_sl_name, sl_type) in
  (* Step 1 -- this is our context *)
  let ctxt = {summary; break_lbl= None; uenv; senv; gdecls} in
  (* A buildlet for allocating the locals structure *)
  let build_alloca = B.add_alloca (locals_uid, Namedt locals_tid) in
  (* Aux list of arguments with SL added in the beginning *)
  let args' =
    sl_info
    :: List.map (fun (H.Arg {name; ty; _}) -> (name, ty_to_llty ty)) args
  in
  let copy_one_arg (name, ty) =
    (* A buildlet for copying one argument *)
    let build_gep, op_gep =
      aiwf "arg"
        (gep_0 (* Use GEP to find where to store the argument *)
           (Namedt locals_tid) (Id locals_uid) (offset_of_symbol name) )
    in
    (* Observe how we return the composition of two buildlets *)
    build_gep $> build_store ty (Id name) op_gep
  in
  let copy_args =
    (* A buildlet that copies all of the arguments *)
    List.rev args' |> List.map copy_one_arg |> B.seq_buildlets
  in
  let ret_ty, tr =
    match result with
    | Ty.VOID -> (Void, fun _ -> Ret (Void, None))
    | t ->
        let llty = ty_to_llty t in
        (llty, fun op -> Ret (llty, Some op))
  in
  let build_body, op =
    (* Get the builder for the body and the operand with
       the result; observe that we pass the context. *)
    cgExp ctxt body
  in
  let build_function (* Putting it all together *) =
    build_alloca (* Step 2 *) $> copy_args (* Step 3 *)
    $> build_body (* Step 4 *)
    $> B.term_block (tr op)
  in
  (* Step 5 *)
  let cfg_builder =
    (* Apply the buildlet; we get a cfg_builder *)
    build_function B.empty_cfg_builder
  in
  ( name
  , { fty= (sl_type :: List.map (ty_to_llty <$> ty_of_arg) args, ret_ty)
    ; param= default_sl_name :: List.map name_of_arg args
    ; cfg= B.get_cfg cfg_builder } )

let codegen_prog (H.Program {tdecls; fdecls}) : Ll.prog =
  let tenv = ref UniqueMap.empty in
  let senv = ref SymbolMap.empty in
  let gdecls = ref [] in
  let tdecls1 = List.filter_map (cg_tydecl tenv) tdecls in
  let tdecls2 = List.map (cg_fdecl_summary senv) fdecls in
  let fdecls = List.map (cg_fdecl !senv !tenv gdecls) fdecls in
  let tdecls = tdecls1 @ tdecls2 in
  let gdecls = !gdecls in
  let open Ll in
  {tdecls; gdecls; fdecls}

let runtime_fns =
  let fns =
    [ "i8* @allocRecord(i64)" (* runtime functions *)
    ; "i8* @initArray (i64, i64, i8*)"
    ; "i64 @arrInxError (i64)"
    ; "i64 @recFieldError()"
    ; "i64 @divisionByZero()"
    ; "i64 @stringEqual (i8*, i8*)"
    ; "i64 @stringNotEq (i8*, i8*)"
    ; "i64 @stringLess (i8*, i8*)"
    ; "i64 @stringLessEq (i8*, i8*)"
    ; "i64 @stringGreater (i8*, i8*)"
    ; "i64 @stringGreaterEq (i8*, i8*)"
    ; "i64 @exponent(i64, i64)"
      (* user visible functions; note SL argument *)
    ; "void @print      (i8*, i8*)"
    ; "void @flush      (i8*)"
    ; "i8*  @getChar    (i8*)"
    ; "i64  @ord        (i8*, i8*)"
    ; "i8*  @chr        (i8*, i64)"
    ; "i64  @size       (i8*, i8*)"
    ; "i8*  @substring  (i8*, i8*, i64, i64)"
    ; "i8*  @concat     (i8*, i8*, i8*)"
    ; "i64  @not        (i8*, i64)"
    ; "void @tigerexit  (i8*, i64)" ]
  in
  let mkDeclare s = "declare " ^ s ^ "\n" in
  String.concat "" (List.map mkDeclare fns)

let ll_target_triple : string =
  let ic = Unix.open_process_in "uname" in
  let uname = input_line ic in
  let () = close_in ic in
  match uname with
  | "Darwin" -> "target triple = \"x86_64-apple-macosx10.15.0\""
  | "Linux" -> "target triple = \"x86_64-pc-linux-gnu\""
  | _ -> ""
