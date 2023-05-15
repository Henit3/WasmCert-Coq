From Wasm Require Export common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program.Equality NArith ZArith_base.
From Wasm Require Export typing opsem properties interpreter_func type_progress.

Section intro.

  Variable host_function : eqType.

  Let store_record := store_record host_function.
  Let function_closure := function_closure host_function.
  Let e_typing : store_record -> t_context -> seq administrative_instruction -> function_type -> Prop :=
        @e_typing _.
  Let s_typing := @s_typing host_function.
  Let inst_typing := @inst_typing host_function.
  Let sglob : store_record -> instance -> nat -> option global := @sglob _.
  Let smem_ind : store_record -> instance -> option nat := @smem_ind _.

  Let host := host host_function.

  Variable host_instance : host.

  Let host_state := host_state host_instance.

  Let host_application := @host_application host_function host_instance.

  (* "reduce" checks (state, store, frame, seq -> state, store, frame, seq)? as Prop  *)
  Let reduce : host_state -> store_record -> frame -> seq administrative_instruction ->
               host_state -> store_record -> frame -> seq administrative_instruction -> Prop
      := @reduce _ _.

  (* https://coq.inria.fr/library/Coq.Relations.Relation_Operators.html#clos_refl_trans
   * Uses "clos_refl_trans" with a "reduce_tuple"
   *)
  Let reduce_trans := @reduce_trans host_function host_instance.
  
(*Let config_tuple := config_tuple host_instance.*)

  (* For all (s of type T), Q, P:
   * Hypotheses:
   *  If there exists an s such that (Q s), then P
   *  (Q s)
   * Goal: P
   * Proof:
   *  Exists s in H0. Apply H0 in H1. Apply H1.
   *)
  Lemma test: forall {T: Type} (s: T) Q P ,
      ((exists s, Q s) -> P) -> (Q s) -> P.
  Proof.
    move => T s Q P Himpl HQ.
    apply Himpl; eexists; by apply HQ.
  Qed.
  
      

  
  (* Operational Semantics: Reduction with equivalent base instructions + identical instruction
   * If the base instructions reduce to the same result (i.e. are equivalent),
   *  Appending identical instructions to both sides will still give the same result.
   *)

  Locate "/".
  Search (_ ++ nil). (* cats0 *)
  Search AI_trap.

  (* Reduction of a sequence of commands.
      There's no `explicit` rule that allows this to be possible
      yet this is certainly an expected behaviour.
   *)
  Lemma opsem_reduce_seq1: forall hs1 s1 f1 es1 hs2 s2 f2 es2 es0,
      reduce hs1 s1 f1 es1 hs2 s2 f2 es2 ->
      reduce hs1 s1 f1 (es1 ++ es0) hs2 s2 f2 (es2 ++ es0).
  Proof.
    intros.
    (* (e)Apply r_label yields same proof structure as reduce_composition_right *)
  (*eapply r_label; eauto; apply /lfilledP;
    [instantiate (1 := (LH_base [::] es0)); instantiate (1 := 0)|];
    [replace es1 with ([::] ++ es1) at 2|replace es2 with ([::] ++ es2) at 2];
    reflexivity; apply LfilledBase; reflexivity.*)
  (* or *)
  (*eapply r_label; eauto; apply /lfilledP.
    - instantiate (1 := (LH_base [::] es0)). instantiate (1 := 0).
      replace es1 with ([::] ++ es1) at 2; try (reflexivity).
      apply LfilledBase. reflexivity.
    - replace es2 with ([::] ++ es2) at 2; try (reflexivity).
      apply LfilledBase. reflexivity.*)
    
    (* From type_progress.v, makes use of general reduce_composition *)
    apply reduce_composition_right; assumption.
  (*apply H. *)
  Qed.

  (* Now note that given Wasm's representation of value stack squashed into the instruction list, adding more constants to the bottom of the value stack should not matter as well. *)
  Lemma opsem_reduce_seq2: forall hs1 s1 f1 es1 hs2 s2 f2 es2 vs,
      const_list vs ->
      reduce hs1 s1 f1 es1 hs2 s2 f2 es2 ->
      reduce hs1 s1 f1 (vs ++ es1) hs2 s2 f2 (vs ++ es2).
  Proof.
    intros.
    (* (e)Apply r_label yields same proof structure as reduce_composition_left *)
  (*eapply r_label; eauto; apply /lfilledP;
    [instantiate (1 := (LH_base vs [::])); instantiate (1 := 0)|];
    [replace es1 with (es1 ++ [::]) at 2|replace es2 with (es2 ++ [::]) at 2];
    try (apply cats0); apply LfilledBase; apply H.*)
  (* or *)
  (*eapply r_label; eauto; apply /lfilledP.
    - instantiate (1 := (LH_base vs [::])). instantiate (1 := 0).
      replace es1 with (es1 ++ [::]) at 2; try (apply cats0).
      apply LfilledBase. apply H.
    - replace es2 with (es2 ++ [::]) at 2; try (apply cats0).
      apply LfilledBase. apply H.*)
    
    (* From type_progress.v, makes use of general reduce_composition *)
    apply reduce_composition_left; assumption.
  (*- apply H.
    - apply H0.*)
  Qed.

  (* This lemma can of course be derived from the two above. However, its proof itself is
     even simpler. *)
  Lemma opsem_reduce_seq3: forall hs1 s1 f1 es1 hs2 s2 f2 es2 vs es0,
      const_list vs ->
      reduce hs1 s1 f1 es1 hs2 s2 f2 es2 ->
      reduce hs1 s1 f1 (vs ++ es1 ++ es0) hs2 s2 f2 (vs ++ es2 ++ es0).
  Proof.
    intros.
    (* (e)Apply r_label yields same proof structure as reduce_composition *)
  (*eapply r_label; eauto; apply /lfilledP;
    [instantiate (1 := (LH_base vs es0)); instantiate (1 := 0)|];
    apply LfilledBase; apply H.*)
    (* or *)
  (*eapply r_label; eauto; apply /lfilledP.
    - instantiate (1 := (LH_base vs es0)). instantiate (1 := 0).
      apply LfilledBase. apply H.
    - apply LfilledBase. apply H.*)

    (* From type_progress.v, this is the general reduce_composition form *)
    apply reduce_composition; assumption.
  (*- apply H.
    - apply H0.*)
  Qed.

  
  

(*** DEPRECATED
  (* Typing lemmas *)

  (* An easier one to get started *)

  
  (* In properties.v, there's a proof of another verison of this lemma
      with the goal being the non-constructive exists.
      However, that proof relies on inverting the typing rule,
      which cannot be used here due to the goal being a sigma type
      (try coping the proof and see where it goes wrong;
        the tactic auto_prove_bet has to be copied here as well for that to be observed).
      Find a way to prove this lemma with goal being the sigma-typed exists;
      likely it should be done by an induction on es1 or a destruct of e (or both).
      This might be quite difficult. *)
  Lemma composition_typing_single_sig: forall C es1 e t1s t2s,
    be_typing C (es1 ++ [::e]) (Tf t1s t2s) ->
    { ts & { t1s' & { t2s' & { t3s | t1s = ts ++ t1s' /\
                                       t2s = ts ++ t2s' /\
                                       be_typing C es1 (Tf t1s' t3s) /\
                                       be_typing C [::e] (Tf t3s t2s') }}}}.
  Proof.
  Admitted.

  (* Another composition typing lemma,
      with the second component being a general list instead of just a singleton. *)
  Lemma composition_typing_sig: forall C es1 es2 t1s t2s,
      be_typing C (es1 ++ es2) (Tf t1s t2s) ->
      { ts & { t1s' & { t2s' & { t3s | t1s = ts ++ t1s' /\
                                         t2s = ts ++ t2s' /\
                                         be_typing C es1 (Tf t1s' t3s) /\
                                         be_typing C es2 (Tf t3s t2s') }}}}.
  Proof.
  Admitted.
***)
  


  
  (* Additional opsem practice *)
  (* Here is a simple program that involves loops. Observe the code below. *)
  Definition i32_of_Z (z: Z) := VAL_int32 (Wasm_int.int_of_Z i32m z).

  (* Loop Body (raw pseudocode):
   *  stack.push(locals[0])
   *  stack.push((testop (type: T_i32) (op: TO_eqz)) stack.pop())
   *  if (stack.pop() == (i32) 0): stack.push(BI_br (label: 1))
   *  stack.push(locals[0])
   *  stack.push(locals[1])
   *  stack.push((binop (type: T_i32) (op: Binop_i BOI_add)) stack.pop() stack.pop())
   *  locals[1] = stack.pop()
   *  stack.push(locals[0])
   *  stack.push((i32) 1)
   *  stack.push((binop (type: T_i32) (op: Binop_i BOI_sub)) stack.pop() stack.pop())
   *  locals[0] = stack.pop()
   *)
  (* Loop Body (pseudocode):
   *  Apply TO_eqz (=? 0) to locals[0] (if 0 then 1 else 0)
   *    If this is non-zero, then break loop (i.e. break if locals[0] == 0)
   *  Set locals[1] to the sum of locals[0] and locals[1]
   *  Decrement locals[0]
   *)

  Definition loop_body : seq basic_instruction :=
    [ :: BI_get_local 0; BI_testop T_i32 TO_eqz; BI_br_if 1;
      BI_get_local 0; BI_get_local 1; BI_binop T_i32 (Binop_i BOI_add); BI_set_local 1;
      BI_get_local 0; BI_const (i32_of_Z 1); BI_binop T_i32 (Binop_i BOI_sub); BI_set_local 0
    ].
  
  (* Loop Body (raw pseudocode):
   *  stack.push(label[block]) {ves split: ([stack.push(locals[0])], [])}
   *  stack.push(label[loop]) {ves split: ([stack.push(locals[0])], [])}
   *  (Loop Body)
   *)
  (* Loop Body (pseudocode):
   *  Create a new scope with a while true loop of content: Loop Body
   *  Exit when locals[0] is 0
   *    On exit, locals[1] holds sum of all naturals upto the original locals[0]
   *)
  
  Definition code : seq administrative_instruction :=
    [:: AI_basic (BI_block (Tf [:: T_i32] [:: T_i32]) [:: BI_loop (Tf [:: T_i32] [:: T_i32]) loop_body ]);
     AI_basic (BI_get_local 1)].

  Definition result_place_holder : Z -> seq administrative_instruction :=
    fun n => [:: AI_basic (BI_const (i32_of_Z ( (n*(n+1))/2 )))].
  
  (* Try to work out what it does under the given premises,
      and fill in the above definition that specifies the execution result.
      Proving the reduction might be actually very tedious. *)
    Lemma opsem_reduce_loop: forall hs s f (z:Z),
      (z >= 0)%Z ->
      f.(f_locs) = [:: i32_of_Z z; i32_of_Z 0] ->
      exists f', reduce_trans (hs, s, f, code) (hs, s, f', result_place_holder z).
  Proof.
    intros. rename H into Hzpos. rename H0 into Hstore.
  (*destruct f as [ff_locs ff_inst].
    exists {|
      f_locs := [:: i32_of_Z _; i32_of_Z 0];
      f_inst := ff_inst
    |}.*)
    exists f. (* Same initialisation since equivalent code *)
  (*unfold reduce_trans. unfold opsem.reduce_trans.*)
  (*unfold result_place_holder. unfold code. unfold loop_body.*)
  Admitted.
  

End intro.