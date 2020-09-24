(** Wasm interpreter **)
(* (C) J. Pichon, M. Bodin - see LICENSE.txt *)

From Wasm Require Import common.
From Coq Require Import ZArith.BinInt.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Wasm Require Export operations host type_checker.
Require Import BinNat.

Set Implicit Arguments.
Unset Strict Implicit.

Unset Printing Implicit Defensive.

Inductive res_crash : Type :=
| C_error : res_crash
| C_exhaustion : res_crash.

Scheme Equality for res_crash.
Definition res_crash_eqb c1 c2 := is_left (res_crash_eq_dec c1 c2).
Definition eqres_crashP : Equality.axiom res_crash_eqb :=
  eq_dec_Equality_axiom res_crash_eq_dec.

Canonical Structure res_crash_eqMixin := EqMixin eqres_crashP.
Canonical Structure res_crash_eqType := Eval hnf in EqType res_crash res_crash_eqMixin.

Inductive res : Type :=
| R_crash : res_crash -> res
| R_trap : res
| R_value : list value -> res.

Definition res_eq_dec : forall r1 r2 : res, {r1 = r2} + {r1 <> r2}.
Proof. decidable_equality. Defined.

Definition res_eqb (r1 r2 : res) : bool := res_eq_dec r1 r2.
Definition eqresP : Equality.axiom res_eqb :=
  eq_dec_Equality_axiom res_eq_dec.

Canonical Structure res_eqMixin := EqMixin eqresP.
Canonical Structure res_eqType := Eval hnf in EqType res res_eqMixin.

Section Host_func.

Variable host_function : eqType.
Let host := host host_function.

Variable host_instance : host.

Let store_record := store_record host_function.
Let administrative_instruction := administrative_instruction host_function.
Let host_state := host_state host_instance.

Variable host_application_impl : host_state -> store_record -> function_type -> host_function -> seq value ->
                       (host_state * option (store_record * result)).

Hypothesis host_application_impl_correct :
  (forall hs s ft hf vs hs' hres, (host_application_impl hs s ft hf vs = (hs', hres)) -> host_application hs s ft hf vs hs' hres).

Inductive res_step : Type :=
| RS_crash : res_crash -> res_step
| RS_break : nat -> list value -> res_step
| RS_return : list value -> res_step
| RS_normal : list administrative_instruction -> res_step.

Definition res_step_eq_dec : forall r1 r2 : res_step, {r1 = r2} + {r1 <> r2}.
Proof. decidable_equality. Defined.

Definition res_step_eqb (r1 r2 : res_step) : bool := res_step_eq_dec r1 r2.
Definition eqres_stepP : Equality.axiom res_step_eqb :=
  eq_dec_Equality_axiom res_step_eq_dec.

Canonical Structure res_step_eqMixin := EqMixin eqres_stepP.
Canonical Structure res_step_eqType := Eval hnf in EqType res_step res_step_eqMixin.

Definition crash_error := RS_crash C_error.

Definition depth := nat.

Definition fuel := nat.

Definition config_tuple := ((host_state * store_record * list value * list administrative_instruction)%type).

Definition config_one_tuple_without_e := (host_state * store_record * list value * list value)%type.

Definition res_tuple := (host_state * store_record * list value * res_step)%type.

Fixpoint split_vals (es : list basic_instruction) : ((list value) * (list basic_instruction))%type :=
  match es with
  | (EConst v) :: es' =>
    let: (vs', es'') := split_vals es' in
    (v :: vs', es'')
  | _ => ([::], es)
  end.

(** [split_vals_e es]: takes the maximum initial segment of [es] whose elements
    are all of the form [Basic (EConst v)];
    returns a pair of lists [(ves, es')] where [ves] are those [v]'s in that initial
    segment and [es] is the remainder of the original [es]. **)
Fixpoint split_vals_e (es : list administrative_instruction) : ((list value) * (list administrative_instruction))%type :=
  match es with
  | (Basic (EConst v)) :: es' =>
    let: (vs', es'') := split_vals_e es' in
    (v :: vs', es'')
  | _ => ([::], es)
  end.

Fixpoint split_n (es : list value) (n : nat) : ((list value) * (list value))%type :=
  match (es, n) with
  | ([::], _) => ([::], [::])
  | (_, 0) => ([::], es)
  | (e :: esX, n.+1) =>
    let: (es', es'') := split_n esX n in
    (e :: es', es'')
  end.

Definition expect {A B : Type} (ao : option A) (f : A -> B) (b : B) : B :=
  match ao with
  | Some a => f a
  | None => b
  end.

Definition vs_to_es (vs : list value) : list administrative_instruction :=
  v_to_e_list (rev vs).

Definition e_is_trap (e : administrative_instruction) : bool :=
  match e with
  | Trap => true
  | _ => false
  end.

Lemma e_is_trapP : forall e, reflect (e = Trap) (e_is_trap e).
Proof.
  case => //= >; by [ apply: ReflectF | apply: ReflectT ].
Qed.

(** [es_is_trap es] is equivalent to [es == [:: Trap]]. **)
Definition es_is_trap (es : list administrative_instruction) : bool :=
  match es with
  | [::e] => e_is_trap e
  | _ => false
  end.

Lemma es_is_trapP : forall l, reflect (l = [::Trap]) (es_is_trap l).
Proof.
  case; first by apply: ReflectF.
  move=> // a l. case l => //=.
  - apply: (iffP (e_is_trapP _)); first by elim.
    by inversion 1.
  - move=> >. by apply: ReflectF.
Qed.

Fixpoint run_step_with_fuel (fuel : fuel) (d : depth) (i : instance) (cfg : config_tuple) : res_tuple :=
  let: (hs, s, vs, es) := cfg in
  match fuel with
  | 0 => (hs, s, vs, RS_crash C_exhaustion)
  | fuel.+1 =>
    let: (ves, es') := split_vals_e es in (** Framing out constants. **)
    match es' with
    | [::] => (hs, s, vs, crash_error)
    | e :: es'' =>
      if e_is_trap e
      then
        if (es'' != [::]) || (ves != [::])
        then (hs, s, vs, RS_normal [::Trap])
        else (hs, s, vs, crash_error)
      else
        let: (hs', s', vs', r) := run_one_step fuel d i (hs, s, vs, (rev ves)) e in
        if r is RS_normal res
        then (hs', s', vs', RS_normal (res ++ es''))
        else (hs', s', vs', r)
    end
  end

with run_one_step (fuel : fuel) (d : depth) (i : instance) (cfg : config_one_tuple_without_e) (e : administrative_instruction) : res_tuple :=
  let: (hs, s, vs, ves) := cfg in
  match fuel with
  | 0 => (hs, s, vs, RS_crash C_exhaustion)
  | fuel.+1 =>
    match e with
    (* unop *)
    | Basic (Unop_i T_i32 iop) =>
      if ves is ConstInt32 c :: ves' then
        (hs, s, vs, RS_normal (vs_to_es ((ConstInt32 (@app_unop_i i32t iop c)) :: ves')))
      else (hs, s, vs, crash_error)
    | Basic (Unop_i T_i64 iop) =>
      if ves is (ConstInt64 c) :: ves' then
        (hs, s, vs, RS_normal (vs_to_es ((ConstInt64 (@app_unop_i i64t iop c)) :: ves')))
      else (hs, s, vs, crash_error)
    | Basic (Unop_i _ _) => (hs, s, vs, crash_error)
    | Basic (Unop_f T_f32 iop) =>
      if ves is (ConstFloat32 c) :: ves' then
        (hs, s, vs, RS_normal (vs_to_es ((ConstFloat32 (@app_unop_f f32t iop c)) :: ves')))
      else (hs, s, vs, crash_error)
    | Basic (Unop_f T_f64 iop) =>
      if ves is (ConstFloat64 c) :: ves' then
        (hs, s, vs, RS_normal (vs_to_es ((ConstFloat64 (@app_unop_f f64t iop c)) :: ves')))
      else (hs, s, vs, crash_error)
    | Basic (Unop_f _ _) => (hs, s, vs, crash_error)
    (* binop *)
    | Basic (Binop_i T_i32 iop) =>
      if ves is (ConstInt32 c2) :: (ConstInt32 c1) :: ves' then
        expect (@app_binop_i i32t iop c1 c2) (fun c =>
            (hs, s, vs, RS_normal (vs_to_es ((ConstInt32 c) :: ves'))))
          (hs, s, vs, RS_normal ((vs_to_es ves') ++ [::Trap]))
      else (hs, s, vs, crash_error)
    | Basic (Binop_i T_i64 iop) =>
      if ves is (ConstInt64 c2) :: (ConstInt64 c1) :: ves' then
        expect (@app_binop_i i64t iop c1 c2) (fun c =>
            (hs, s, vs, RS_normal (vs_to_es ((ConstInt64 c) :: ves'))))
          (hs, s, vs, RS_normal ((vs_to_es ves') ++ [::Trap]))
      else (hs, s, vs, crash_error)
    | Basic (Binop_i _ _) => (hs, s, vs, crash_error)
    | Basic (Binop_f T_f32 fop) =>
      if ves is (ConstFloat32 c2) :: (ConstFloat32 c1) :: ves' then
        expect (@app_binop_f f32t fop c1 c2) (fun c =>
            (hs, s, vs, RS_normal (vs_to_es ((ConstFloat32 c) :: ves'))))
          (hs, s, vs, RS_normal ((vs_to_es ves') ++ [::Trap]))
      else (hs, s, vs, crash_error)
    | Basic (Binop_f T_f64 fop) =>
      if ves is (ConstFloat64 c2) :: (ConstFloat64 c1) :: ves' then
        expect (@app_binop_f f64t fop c1 c2) (fun c =>
             (hs, s, vs, RS_normal (vs_to_es ((ConstFloat64 c) :: ves'))))
          (hs, s, vs, RS_normal ((vs_to_es ves') ++ [::Trap]))
      else (hs, s, vs, crash_error)
    | Basic (Binop_f _ _) => (hs, s, vs, crash_error)
    (* testops *)
    | Basic (Testop T_i32 testop) =>
      if ves is (ConstInt32 c) :: ves' then
        (hs, s, vs, RS_normal (vs_to_es ((ConstInt32 (wasm_bool (@app_testop_i i32t testop c))) :: ves')))
      else (hs, s, vs, crash_error)
    | Basic (Testop T_i64 testop) =>
      if ves is (ConstInt64 c) :: ves' then
        (hs, s, vs, RS_normal (vs_to_es ((ConstInt32 (wasm_bool (@app_testop_i i64t testop c))) :: ves')))
      else (hs, s, vs, crash_error)
    | Basic (Testop _ _) => (hs, s, vs, crash_error)
    (* relops *)
    | Basic (Relop_i T_i32 iop) =>
      if ves is (ConstInt32 c2) :: (ConstInt32 c1) :: ves' then
        (hs, s, vs, RS_normal (vs_to_es (ConstInt32 (wasm_bool (@app_relop_i i32t iop c1 c2)) :: ves')))
      else (hs, s, vs, crash_error)
    | Basic (Relop_i T_i64 iop) =>
      if ves is (ConstInt64 c2) :: (ConstInt64 c1) :: ves' then
        (hs, s, vs, RS_normal (vs_to_es (ConstInt32 (wasm_bool (@app_relop_i i64t iop c1 c2)) :: ves')))
      else (hs, s, vs, crash_error)
    | Basic (Relop_i _ _) => (hs, s, vs, crash_error)
    | Basic (Relop_f T_f32 iop) =>
      if ves is (ConstFloat32 c2) :: (ConstFloat32 c1) :: ves' then
        (hs, s, vs, RS_normal (vs_to_es (ConstInt32 (wasm_bool (@app_relop_f f32t iop c1 c2)) :: ves')))
      else (hs, s, vs, crash_error)
    | Basic (Relop_f T_f64 iop) =>
      if ves is (ConstFloat64 c2) :: (ConstFloat64 c1) :: ves' then
        (hs, s, vs, RS_normal (vs_to_es (ConstInt32 (wasm_bool (@app_relop_f f64t iop c1 c2)) :: ves')))
      else (hs, s, vs, crash_error)
    | Basic (Relop_f _ _) => (hs, s, vs, crash_error)
    (* convert & reinterpret *)
    | Basic (Cvtop t2 Convert t1 sx) =>
      if ves is v :: ves' then
        if types_agree t1 v
        then
          expect (cvt t2 sx v) (fun v' =>
               (hs, s, vs, RS_normal (vs_to_es (v' :: ves'))))
            (hs, s, vs, RS_normal ((vs_to_es ves') ++ [::Trap]))
        else (hs, s, vs, crash_error)
      else (hs, s, vs, crash_error)
    | Basic (Cvtop t2 Reinterpret t1 sx) =>
      if ves is v :: ves' then
        if types_agree t1 v && (sx == None)
        then (hs, s, vs, RS_normal (vs_to_es (wasm_deserialise (bits v) t2 :: ves')))
        else (hs, s, vs, crash_error)
      else (hs, s, vs, crash_error)
    (**)
    | Basic Unreachable => (hs, s, vs, RS_normal ((vs_to_es ves) ++ [::Trap]))
    | Basic Nop => (hs, s, vs, RS_normal (vs_to_es ves))
    | Basic Drop =>
      if ves is v :: ves' then
        (hs, s, vs, RS_normal (vs_to_es ves'))
      else (hs, s, vs, crash_error)
    | Basic Select =>
      if ves is (ConstInt32 c) :: v2 :: v1 :: ves' then
        if c == Wasm_int.int_zero i32m
        then (hs, s, vs, RS_normal (vs_to_es (v2 :: ves')))
        else (hs, s, vs, RS_normal (vs_to_es (v1 :: ves')))
      else (hs, s, vs, crash_error)
    | Basic (Block (Tf t1s t2s) es) =>
      if length ves >= length t1s
      then
        let: (ves', ves'')  := split_n ves (length t1s) in
        (hs, s, vs, RS_normal (vs_to_es ves''
                ++ [::Label (length t2s) [::] (vs_to_es ves' ++ to_e_list es)]))
      else (hs, s, vs, crash_error)
    | Basic (Loop (Tf t1s t2s) es) =>
      if length ves >= length t1s
      then
        let: (ves', ves'') := split_n ves (length t1s) in
        (hs, s, vs, RS_normal (vs_to_es ves''
                ++ [::Label (length t1s) [::Basic (Loop (Tf t1s t2s) es)]
                        (vs_to_es ves' ++ to_e_list es)]))
      else (hs, s, vs, crash_error)
    | Basic (If tf es1 es2) =>
      if ves is ConstInt32 c :: ves' then
        if c == Wasm_int.int_zero i32m
        then (hs, s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Block tf es2)]))
        else (hs, s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Block tf es1)]))
      else (hs, s, vs, crash_error)
    | Basic (Br j) => (hs, s, vs, RS_break j ves)
    | Basic (Br_if j) =>
      if ves is ConstInt32 c :: ves' then
        if c == Wasm_int.int_zero i32m
        then (hs, s, vs, RS_normal (vs_to_es ves'))
        else (hs, s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Br j)]))
      else (hs, s, vs, crash_error)
    | Basic (Br_table js j) =>
      if ves is ConstInt32 c :: ves' then
        let: k := Wasm_int.nat_of_uint i32m c in
        if k < length js
        then
          expect (List.nth_error js k) (fun js_at_k =>
              (hs, s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Br js_at_k)])))
            (hs, s, vs, crash_error)
        else (hs, s, vs, RS_normal (vs_to_es ves' ++ [::Basic (Br j)]))
      else (hs, s, vs, crash_error)
    | Basic (Call j) =>
      if sfunc s i j is Some sfunc_i_j then
        (hs, s, vs, RS_normal (vs_to_es ves ++ [::Invoke sfunc_i_j]))
      else (hs, s, vs, crash_error)
    | Basic (Call_indirect j) =>
      if ves is ConstInt32 c :: ves' then
        match stab s i (Wasm_int.N_of_uint i32m c) with
        | Some cl =>
          if stypes s i j == Some (cl_type cl)
          then (hs, s, vs, RS_normal (vs_to_es ves' ++ [::Invoke cl]))
          else (hs, s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
        | None => (hs, s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
        end
      else (hs, s, vs, crash_error)
    | Basic Return => (hs, s, vs, RS_return ves)
    | Basic (Get_local j) =>
      if j < length vs
      then
        expect (List.nth_error vs j) (fun vs_at_j =>
            (hs, s, vs, RS_normal (vs_to_es (vs_at_j :: ves))))
          (hs, s, vs, crash_error)
      else (hs, s, vs, crash_error)
    | Basic (Set_local j) =>
      if ves is v :: ves' then
        if j < length vs
        then (hs, s, update_list_at vs j v, RS_normal (vs_to_es ves'))
        else (hs, s, vs, crash_error)
      else (hs, s, vs, crash_error)
    | Basic (Tee_local j) =>
      if ves is v :: ves' then
        (hs, s, vs, RS_normal (vs_to_es (v :: ves) ++ [::Basic (Set_local j)]))
      else (hs, s, vs, crash_error)
    | Basic (Get_global j) =>
      if sglob_val s i j is Some xx
      then (hs, s, vs, RS_normal (vs_to_es (xx :: ves)))
      else (hs, s, vs, crash_error)
    | Basic (Set_global j) =>
      if ves is v :: ves' then
        if supdate_glob s i j v is Some xx
        then (hs, xx, vs, RS_normal (vs_to_es ves'))
        else (hs, s, vs, crash_error)
      else (hs, s, vs, crash_error)
    | Basic (Load t None a off) =>
      if ves is ConstInt32 k :: ves' then
        expect
          (smem_ind s i)
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load (mem_s_j) (Wasm_int.N_of_uint i32m k) off (t_length t))
                 (fun bs => (hs, s, vs, RS_normal (vs_to_es (wasm_deserialise bs t :: ves'))))
                 (hs, s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
             else (hs, s, vs, crash_error))
          (hs, s, vs, crash_error)
      else (hs, s, vs, crash_error)
    | Basic (Load t (Some (tp, sx)) a off) =>
      if ves is ConstInt32 k :: ves' then
        expect
          (smem_ind s i)
          (fun j =>
             if List.nth_error s.(s_mems) j is Some mem_s_j then
               expect
                 (load_packed sx (mem_s_j) (Wasm_int.N_of_uint i32m k) off (tp_length tp) (t_length t))
                 (fun bs => (hs, s, vs, RS_normal (vs_to_es (wasm_deserialise bs t :: ves'))))
                 (hs, s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
             else (hs, s, vs, crash_error))
          (hs, s, vs, crash_error)
      else (hs, s, vs, crash_error)
    | Basic (Store t None a off) =>
      if ves is v :: ConstInt32 k :: ves' then
        if types_agree t v
        then
          expect
            (smem_ind s i)
            (fun j =>
               if List.nth_error s.(s_mems) j is Some mem_s_j then
                 expect
                   (store mem_s_j (Wasm_int.N_of_uint i32m k) off (bits v) (t_length t))
                   (fun mem' =>
                      (hs, upd_s_mem s (update_list_at s.(s_mems) j mem'), vs, RS_normal (vs_to_es ves')))
                   (hs, s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
               else (hs, s, vs, crash_error))
            (hs, s, vs, crash_error)
        else (hs, s, vs, crash_error)
      else (hs, s, vs, crash_error)
    | Basic (Store t (Some tp) a off) =>
      if ves is v :: ConstInt32 k :: ves' then
        if types_agree t v
        then
          expect
            (smem_ind s i)
            (fun j =>
               if List.nth_error s.(s_mems) j is Some mem_s_j then
                 expect
                   (store_packed mem_s_j (Wasm_int.N_of_uint i32m k) off (bits v) (tp_length tp))
                   (fun mem' =>
                      (hs, upd_s_mem s (update_list_at s.(s_mems) j mem'), vs, RS_normal (vs_to_es ves')))
                   (hs, s, vs, RS_normal (vs_to_es ves' ++ [::Trap]))
               else (hs, s, vs, crash_error))
            (hs, s, vs, crash_error)
        else (hs, s, vs, crash_error)
      else (hs, s, vs, crash_error)
    | Basic Current_memory =>
      expect
        (smem_ind s i)
        (fun j =>
           if List.nth_error s.(s_mems) j is Some s_mem_s_j then
             (hs, s, vs, RS_normal (vs_to_es (ConstInt32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size s_mem_s_j))) :: ves)))
           else (hs, s, vs, crash_error))
        (hs, s, vs, crash_error)
    | Basic Grow_memory =>
      if ves is ConstInt32 c :: ves' then
        expect
          (smem_ind s i)
          (fun j =>
            if List.nth_error s.(s_mems) j is Some s_mem_s_j then
              let: l := mem_size s_mem_s_j in
              let: mem' := mem_grow s_mem_s_j (Wasm_int.N_of_uint i32m c) in
              if mem' is Some mem'' then
                (hs, upd_s_mem s (update_list_at s.(s_mems) j mem''), vs,
                 RS_normal (vs_to_es (ConstInt32 (Wasm_int.int_of_Z i32m (Z.of_nat l)) :: ves')))
              else (hs, s, vs, crash_error)
            else (hs, s, vs, crash_error))
          (hs, s, vs, crash_error)
      else (hs, s, vs, crash_error)
    | Basic (EConst _) => (hs, s, vs, crash_error)
    | Invoke cl =>
      match cl with
      | Func_native i' (Tf t1s t2s) ts es =>
        let: n := length t1s in
        let: m := length t2s in
        if length ves >= n
        then
          let: (ves', ves'') := split_n ves n in
          let: zs := n_zeros ts in
          (hs, s, vs, RS_normal (vs_to_es ves''
                  ++ [::Local m i' (rev ves' ++ zs) [::Basic (Block (Tf [::] t2s) es)]]))
        else (hs, s, vs, crash_error)
      | Func_host (Tf t1s t2s) f =>
        let: n := length t1s in
        let: m := length t2s in
        if length ves >= n
        then
          let: (ves', ves'') := split_n ves n in
          match host_application_impl hs s (Tf t1s t2s) f (rev ves') with
          | (hs', Some (s', rves)) =>
            (hs', s', vs, RS_normal (vs_to_es ves'' ++ (result_to_stack rves)))
          | (hs', None) => (hs', s, vs, RS_normal (vs_to_es ves'' ++ [::Trap]))
          end
        else (hs, s, vs, crash_error)
      end
    | Label ln les es =>
      if es_is_trap es
      then (hs, s, vs, RS_normal (vs_to_es ves ++ [::Trap]))
      else
        if const_list es
        then (hs, s, vs, RS_normal (vs_to_es ves ++ es))
        else
          let: (hs', s', vs', res) := run_step_with_fuel fuel d i (hs, s, vs, es) in
          match res with
          | RS_break 0 bvs =>
            if length bvs >= ln
            then (hs', s', vs', RS_normal ((vs_to_es ((take ln bvs) ++ ves)) ++ les))
            else (hs', s', vs', crash_error)
          | RS_break (n.+1) bvs => (hs', s', vs', RS_break n bvs)
          | RS_return rvs => (hs', s', vs', RS_return rvs)
          | RS_normal es' =>
            (hs', s', vs', RS_normal (vs_to_es ves ++ [::Label ln les es']))
          | RS_crash error => (hs', s', vs', RS_crash error)
          end
    | Local ln j vls es =>
      if es_is_trap es
      then (hs, s, vs, RS_normal (vs_to_es ves ++ [::Trap]))
      else
        if const_list es
        then
          if length es == ln
          then (hs, s, vs, RS_normal (vs_to_es ves ++ es))
          else (hs, s, vs, crash_error)
        else
          let: (hs', s', vls', res) := run_step_with_fuel fuel d j (hs, s, vls, es) in
          match res with
          | RS_return rvs =>
            if length rvs >= ln
            then (hs', s', vs, RS_normal (vs_to_es (take ln rvs ++ ves)))
            else (hs', s', vs, crash_error)
          | RS_normal es' =>
            (hs', s', vs, RS_normal (vs_to_es ves ++ [::Local ln j vls' es']))
          | RS_crash error => (hs', s', vs, RS_crash error)
          | RS_break _ _ => (hs', s', vs, crash_error)
          end
    | Trap => (hs, s, vs, crash_error)
    end
  end.

(** Enough fuel so that [run_one_step] does not run out of exhaustion. **)
Definition run_one_step_fuel : administrative_instruction -> nat.
Proof.
  move=> es. induction es using administrative_instruction_rect';
    let rec aux v :=
      lazymatch goal with
      | F : TProp.Forall _ _ |- _ =>
        apply TProp.max in F;
        move: F;
        let n := fresh "n" in
        move=> n;
        aux (n + v)
      | |- _ => exact (v.+1)
      end in
    aux (1 : nat).
Defined.

(** Enough fuel so that [run_step] does not run out of exhaustion. **)
Definition run_step_fuel (cfg : config_tuple) : nat :=
  let: (hs, s, vs, es) := cfg in
  1 + List.fold_left max (List.map run_one_step_fuel es) 0.

Definition run_step (d : depth) (inst : instance) (cfg : config_tuple) : res_tuple :=
  run_step_with_fuel (run_step_fuel cfg) d inst cfg.

Fixpoint run_v (fuel : fuel) (d : depth) (i : instance) (cfg : config_tuple) : ((host_state * store_record * res)%type) :=
  let: (hs, s, vs, es) := cfg in
  match fuel with
  | 0 => (hs, s, R_crash C_exhaustion)
  | fuel.+1 =>
    if es_is_trap es
    then (hs, s, R_trap)
    else
      if const_list es
      then (hs, s, R_value (fst (split_vals_e es)))
      else
        let: (hs', s', vs', res) := run_step d i (hs, s, vs, es) in
        match res with
        | RS_normal es' => run_v fuel d i (hs', s', vs', es')
        | RS_crash error => (hs', s', R_crash error)
        | _ => (hs', s', R_crash C_error)
        end
  end.

End Host_func.