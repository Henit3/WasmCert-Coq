(** Proof of progress **)
(* (C) Rao Xiaojia, M. Bodin - see LICENSE.txt *)

From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program.Equality NArith Omega.
From Wasm Require Export operations typing datatypes_properties typing opsem properties type_preservation tactics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Variable host_function : eqType.

Let store_record := store_record host_function.
Let function_closure := function_closure host_function.
Let e_typing : store_record -> t_context -> seq administrative_instruction -> function_type -> Prop :=
  @e_typing _.
Let s_typing := @s_typing host_function.
Let inst_typing := @inst_typing host_function.
Let sglob : store_record -> instance -> nat -> option globalinst := @sglob _.
Let smem_ind : store_record -> instance -> option memaddr := @smem_ind _.

Let host := host host_function.

Variable host_instance : host.

Let host_state := host_state host_instance.

Let host_application := @host_application host_function host_instance.

Let reduce : host_state -> store_record -> frame -> seq administrative_instruction ->
             host_state -> store_record -> frame -> seq administrative_instruction -> Prop
  := @reduce _ _.

Definition terminal_form (es: seq administrative_instruction) :=
  const_list es \/ es = [::AI_trap].

Lemma reduce_trap_left: forall vs,
    const_list vs ->
    vs <> [::] ->
    reduce_simple (vs ++ [::AI_trap]) [::AI_trap].
Proof.
  move => vs HConst H.
  apply const_es_exists in HConst as [vs' Hconst].
  eapply rs_trap; first by repeat destruct vs => //.
  instantiate (1 := LH_base vs' [::]).
  unfold lfilled => /=; subst; by apply/eqP.
Qed.

Lemma v_e_trap: forall vs es,
    const_list vs ->
    vs ++ es = [::AI_trap] ->
    vs = [::] /\ es = [::AI_trap].
Proof.
  move => vs es HConst H.
  destruct vs => //=.
  destruct vs => //=. destruct es => //=.
  simpl in H. inversion H. by subst.
Qed.

Lemma cat_split: forall {X:Type} (l l1 l2: seq X),
    l = l1 ++ l2 ->
    l1 = take (size l1) l /\
    l2 = drop (size l1) l.
Proof.
  move => X l l1.
  generalize dependent l.
  induction l1 => //=; move => l l2 HCat; subst => //=.
  - split. by rewrite take0. by rewrite drop0.
  - edestruct IHl1.
    instantiate (1 := l2). eauto.
    split => //.
    by f_equal.
Qed.

Lemma reduce_composition: forall s cs f es es0 s' f' es' hs hs',
    const_list cs ->
    reduce hs s f es hs' s' f' es' ->
    reduce hs s f (cs ++ es ++ es0) hs' s' f' (cs ++ es' ++ es0).
Proof.
  move => s cs f es es0 s' f' es' hs hs' HConst HReduce.
  apply const_es_exists in HConst as [vs' Hconst].
  eapply r_label with (lh := (LH_base vs' es0)); eauto; unfold lfilled => /=; apply/eqP; by subst.
Qed.

Lemma reduce_composition_right: forall s f es es0 s' f' es' hs hs',
    reduce hs s f es hs' s' f' es' ->
    reduce hs s f (es ++ es0) hs' s' f' (es' ++ es0).
Proof.
  move => s f es es0 s' f' es' hs hs' HReduce.
  eapply reduce_composition in HReduce.
  instantiate (1 := es0) in HReduce.
  instantiate (1 := [::]) in HReduce.
  by simpl in HReduce.
  by [].
Qed.

Lemma reduce_composition_left: forall s cs f es s' f' es' hs hs',
    const_list cs ->
    reduce hs s f es hs' s' f' es' ->
    reduce hs s f (cs ++ es) hs' s' f' (cs ++ es').
Proof.
  move => s f es es0 s' f' es' hs hs' HConst HReduce.
  eapply reduce_composition in HReduce; eauto.
  instantiate (1 := [::]) in HReduce.
  by repeat rewrite cats0 in HReduce.
Qed.

Lemma lfilled0_empty: forall es,
    lfilled (LH_base [::] [::]) es es.
Proof.
  move => es.
  unfold lfilled. apply/eqP => /=. by simplify_lists.
Qed.

Lemma label_lfilled1: forall n es es0,
    lfilled (LH_rec [::] n es0 (LH_base [::] [::]) [::]) es [::AI_label n es0 es].
Proof.
  move => n es es0.
  unfold lfilled. apply/eqP => /=. by simplify_lists.
Qed.

Lemma terminal_form_v_e: forall vs es,
    const_list vs ->
    terminal_form (vs ++ es) ->
    terminal_form es.
Proof.
  move => vs es HConst HTerm.
  unfold terminal_form in HTerm.
  destruct HTerm.
  - unfold terminal_form. left.
    apply const_list_split in H. by destruct H.
  - destruct vs => //=.
    + simpl in H. subst. unfold terminal_form. by right.
    + destruct vs => //=. destruct es => //=.
      simpl in H. inversion H. by subst.
Qed.

Lemma terminal_trap: terminal_form [::AI_trap].
Proof.
  unfold terminal_form. by right.
Qed.

Lemma typeof_append: forall ts t vs,
    map typeof vs = ts ++ [::t] ->
    exists v,
      vs = take (size ts) vs ++ [::v] /\
      map typeof (take (size ts) vs) = ts /\
      typeof v = t.
Proof.
  move => ts t vs HMapType.
  apply cat_split in HMapType.
  destruct HMapType.
  rewrite -map_take in H.
  rewrite -map_drop in H0.
  destruct (drop (size ts) vs) eqn:HDrop => //=.
  destruct l => //=.
  inversion H0. subst.
  exists v.
  split => //.
  rewrite -HDrop. by rewrite cat_take_drop.
Qed.

Hint Constructors reduce_simple : core.
Hint Constructors opsem.reduce_simple : core.

Ltac invert_typeof_vcs :=
  lazymatch goal with
  | H: map typeof ?vcs = [::_; _; _] |- _ =>
    destruct vcs => //=; destruct vcs => //=; destruct vcs => //=; destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  | H: map typeof ?vcs = [::_; _] |- _ =>
    destruct vcs => //=; destruct vcs => //=; destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  | H: map typeof ?vcs = [::_] |- _ =>
    destruct vcs => //=; destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  | H: map typeof ?vcs = [::] |- _ =>
    destruct vcs => //=;
    simpl in H; inversion H; subst; clear H
  end.

Lemma nth_error_map: forall {X Y:Type} (l: seq X) n f {fx: Y},
    List.nth_error (map f l) n = Some fx ->
    exists x, List.nth_error l n = Some x /\
    f x = fx.
Proof.
  move => X Y l n.
  generalize dependent l.
  induction n => //; move => l f fx HN.
  - destruct l => //=.
    simpl in HN. inversion HN. subst. by eauto.
  - destruct l => //=.
    simpl in HN. by apply IHn.
Qed.

(* TODO: fix the rest of progress *)

(* tc_func_t -> tc_func *)
(* Remember fails: extra destructs. *)
Lemma func_context_store: forall s i C j x,
    inst_typing s i C ->
    j < length (tc_func C) ->
    List.nth_error (tc_func C) j = Some x ->
    exists a, List.nth_error i.(inst_funcs) j = Some a.
Proof.
  (* TODO: inst_funcs is a fragile name *)
  move => s i C j x HIT HLength HN.
  unfold sfunc. unfold operations.sfunc. unfold option_bind.
  unfold sfunc_ind.
  unfold inst_typing, typing.inst_typing in HIT.
  destruct i => //=. destruct C => //=.
  destruct tc_elem => //=. destruct tc_data => //=. destruct tc_local => //=.
  destruct tc_label => //=. destruct tc_return => //=. destruct tc_ref => //=.
  remove_bools_options.
  remember H3 as H4. clear HeqH4.
  apply all2_size in H3.
  repeat rewrite -length_is_size in H3.
  simpl in HLength.
  rewrite -H3 in HLength.
  move/ltP in HLength.
  apply List.nth_error_Some in HLength.
  destruct (List.nth_error inst_funcs j) eqn:HN1 => //=.
  by eexists.
Qed.

(* inst_globs -> inst_globals *)
(* globals_agree -> globali_agree
   This no longer has the (n < length gs) condition that was used here
*)
Lemma glob_context_store: forall s i C j g,
    inst_typing s i C ->
    j < length (tc_global C) ->
    List.nth_error (tc_global C) j = Some g ->
    sglob s i j <> None.
Proof.
  (* TODO: inst_globs is a fragile name *)
  move => s i C j g HIT HLength HN.
  unfold sglob. unfold operations.sglob. unfold option_bind.
  unfold sglob_ind.
  unfold inst_typing, typing.inst_typing in HIT.
  destruct i => //=. destruct C => //=.
  destruct tc_elem => //=. destruct tc_data => //=. destruct tc_local => //=.
  destruct tc_label => //=. destruct tc_return => //=. destruct tc_ref => //=.
  remove_bools_options.
  remember H2 as H4. clear HeqH4.
  apply all2_size in H2.
  repeat rewrite -length_is_size in H2.
  simpl in HLength.
  rewrite -H2 in HLength.
  move/ltP in HLength.
  apply List.nth_error_Some in HLength.
  destruct (List.nth_error inst_globals j) eqn:HN1 => //=.
  apply List.nth_error_Some.
  unfold globali_agree in H4.
  eapply all2_projection in H4; eauto.
  remove_bools_options.
  apply List.nth_error_Some.
  unfold lookup_N in Hoption.
  rewrite Hoption.
  discriminate.
Qed.


(* expects (N.to_nat m) but given m *)
(* Old disregarded N.to_nat n
Lemma mem_context_store: forall s i C,
    inst_typing s i C ->
    tc_memory C <> [::] ->
    exists n, smem_ind s i = Some n /\
              List.nth_error (s_mems s) n <> None. *)
Lemma mem_context_store: forall s i C,
    inst_typing s i C ->
    tc_memory C <> [::] ->
    exists n, smem_ind s i = Some n /\
              List.nth_error (s_mems s) (N.to_nat n) <> None.
Proof.
  (* TODO: inst_memory is a fragile name *)
  move => s i C HIT HMemory.
  unfold inst_typing, typing.inst_typing in HIT.
  destruct i => //=. destruct C => //=.
  destruct tc_elem => //=. destruct tc_data => //=. destruct tc_local => //=.
  destruct tc_label => //=. destruct tc_return => //=. destruct tc_ref => //=.
  remove_bools_options.
  simpl in HMemory. unfold smem_ind. simpl.
  remember H0 as H4. clear HeqH4.
  apply all2_size in H0.
  destruct inst_mems => //=; first by destruct tc_memory.
  exists m. split => //.
  destruct tc_memory => //.
  simpl in H4.
  unfold memi_agree in H4.
  unfold option_map in H4.
  unfold lookup_N in H4.
  by remove_bools_options.
Qed.

(* Rewrite based off r_call_indirect_success *)
Lemma store_typing_stabaddr: forall s f C c a i,
  stab_elem s f.(f_inst) c (Wasm_int.nat_of_uint i32m i) = Some (VAL_ref_func a) ->
  inst_typing s f.(f_inst) C ->
  store_typing s ->
  exists cl, lookup_N s.(s_funcs) a = Some cl.
Proof.
  move => s f C c a i HStab HIT HST.
  unfold inst_typing, typing.inst_typing in HIT.
  unfold store_typing, tab_agree, tabcl_agree in HST.
  unfold stab_elem in HStab.
  destruct s => //=. destruct f => //=. destruct f_inst. destruct f_inst. destruct C => //=.
  destruct tc_elem => //=. destruct tc_data => //=. destruct tc_local => //=.
  destruct tc_label => //=. destruct tc_return => //=. destruct tc_ref => //=.
  remove_bools_options. simpl in *.
  unfold stab in Hoption. unfold option_bind in HStab.
  remove_bools_options.
  subst. simpl in *.
  remove_bools_options.
  destruct HST.
  destruct H4.
  rewrite -> List.Forall_forall in H4.
  assert (HIN1: List.In t s_tables).
  { by apply List.nth_error_In in Hoption. }
  apply H4 in HIN1. destruct HIN1 as [HIN1 ?].
  rewrite -> List.Forall_forall in HIN1.
  assert (HIN2: List.In (VAL_ref_func a) (tableinst_elem t)).
  { by apply List.nth_error_In in HStab. }
  apply HIN1 in HIN2.
  destruct HIN2 as [HIN2 _].
  move/ltP in HIN2.
  apply List.nth_error_Some in HIN2.
  destruct (List.nth_error s_funcs (N.to_nat a)) eqn:HNth => //;
  fold (lookup_N s_funcs a) in HNth.
  by exists f.
Qed.


(*
  Except [::BI_br i] or [::Return], every other basic instruction can be
    prepended by several consts to be reduceable to something else.

  Although we only actually need bes to be not Return or BI_br, we have to state an
    entire lfilled proposition as a condition due to composition.
 *)

(* TODO: lfilled definition changed
  Not lfilled at depth n with lholed for n-1 containing br, followed by es
*)
Definition not_lf_br (es: seq administrative_instruction) (n: nat) :=
  forall k (lh : lholed n), ~ lfilled lh [::AI_basic (BI_br k)] es.

Definition not_lf_return (es: seq administrative_instruction) (n: nat) :=
  forall (lh : lholed n), ~ lfilled lh [::AI_basic BI_return] es.

Lemma lf_composition: forall es es2 e0 n (lh : lholed n),
    lfilled lh e0 es ->
    exists (lh' : lholed n), lfilled lh' e0 (es ++ es2).
Proof.
  move => es es2 e0 n lh HLF.
  destruct lh as [vs es' | n0 vs l es' lh' es''];
  [ exists (LH_base vs (es' ++ es2))
  | exists (LH_rec vs l es' lh' (es'' ++ es2))];
    unfold lfilled in *; simpl in *;
    apply/eqP; move/eqP in HLF; rewrite <- HLF;
    by repeat rewrite -catA.
Qed.

(* lholed 0 now defined as vs -> ais -> lh instead of ais -> ais -> lh
   May need e_to_v_list? This gives seq of option though

   Definition e_to_v_list (es : list administrative_instruction) : seq (option value) :=
    map e_to_v es.
*)

Lemma lf_composition_left: forall cs es e0 n (lh : lholed n),
    const_list cs ->
    lfilled lh e0 es ->
    exists (lh' : lholed n), lfilled lh' e0 (cs ++ es).
Proof.
  move => cs es e0 n lh HConst HLF.
  apply const_list_get in HConst. destruct HConst.
  destruct lh as [vs es' | n0 vs l es' lh' es''].
  - exists (LH_base (x ++ vs) es').
    unfold lfilled in *; simpl in *;
    apply/eqP; move/eqP in HLF; rewrite <- HLF.
    rewrite <- v_to_e_cat. rewrite H. by rewrite <- catA.
  - exists (LH_rec (x ++ vs) l es' lh' es'').
    unfold lfilled in *; simpl in *;
    apply/eqP; move/eqP in HLF; rewrite <- HLF.
    rewrite <- v_to_e_cat. rewrite H. by rewrite catA.
Qed.


Lemma nlfbr_right: forall es n es',
    not_lf_br (es ++ es') n ->
    not_lf_br es n.
Proof.
  move => es n es' HNLF k lh HContra.
  eapply lf_composition in HContra.
  instantiate (1 := es') in HContra.
  destruct HContra.
  by eapply HNLF; eauto.
Qed.

Lemma nlfret_right: forall es n es',
    not_lf_return (es ++ es') n ->
    not_lf_return es n.
Proof.
  move => es n es' HNLF lh HContra.
  eapply lf_composition in HContra.
  instantiate (1 := es') in HContra.
  destruct HContra.
  by eapply HNLF; eauto.
Qed.

Lemma nlfbr_left: forall es n cs,
    const_list cs ->
    not_lf_br (cs ++ es) n ->
    not_lf_br es n.
Proof.
  move => es n cs HConst HNLF k lh HContra.
  eapply lf_composition_left in HContra => //.
  {
    instantiate (1 := cs) in HContra.
    destruct HContra.
    by eapply HNLF; eauto.
  }
  by [].
Qed.

Lemma nlfret_left: forall es n cs,
    const_list cs ->
    not_lf_return (cs ++ es) n ->
    not_lf_return es n.
Proof.
  move => es n cs HConst HNLF lh HContra.
  eapply lf_composition_left in HContra => //.
  {
    instantiate (1 := cs) in HContra.
    destruct HContra.
    by eapply HNLF; eauto.
  }
  by [].
Qed.

(*
  The version in properties.v cannot be applied since we need to apply this lemma
    on the version of to_e_list with host (defined in this section).
  Interestingly enough, Coq somehow allows the statement to be proved trivially
    by invoking the same lemma in properties.v (but not allowing the application
    of that lemma directly?... 
*)
Lemma to_e_list_cat: forall l1 l2,
    to_e_list (l1 ++ l2) = to_e_list l1 ++ to_e_list l2.
Proof.
    by apply properties.to_e_list_cat.
Qed.

(* TODO: find better fixes than the current duplication. *)
Ltac split_et_composition:=
  lazymatch goal with
  | H: e_typing _ _ (_ ++ _) _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let t2s := fresh "t2s" in
    let t3s := fresh "t3s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply e_composition_typing in H;
    destruct H as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]]; subst
  | H: typing.e_typing _ _ (_ ++ _) _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let t2s := fresh "t2s" in
    let t3s := fresh "t3s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply e_composition_typing in H;
    destruct H as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]]; subst
  end.

(* different from type_preservation in current state *)
Ltac invert_e_typing:=
  repeat lazymatch goal with
  | H: e_typing _ _ (_ ++ _) _ |- _ =>
    split_et_composition
  | H: typing.e_typing _ _ (_ ++ _) _ |- _ =>
    split_et_composition
  | H: e_typing _ _ [::AI_label _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Label_typing in H;
    destruct H as [ts [t1s [H1 [H2 [H3 H4]]]]]; subst
  | H: typing.e_typing _ _ [::AI_label _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    eapply Label_typing in H; eauto;
    destruct H as [ts [t1s [H1 [H2 [H3 H4]]]]]; subst
         end.

Ltac auto_basic :=
  repeat lazymatch goal with
  | |- es_is_basic [::AI_basic _; AI_basic _; AI_basic _; AI_basic _] =>
    apply List.Forall_cons => //=
  | |- es_is_basic [::AI_basic _; AI_basic _; AI_basic _] =>
    apply List.Forall_cons => //=
  | |- es_is_basic [::AI_basic _; AI_basic _] =>
    apply List.Forall_cons => //=
  | |- es_is_basic [::AI_basic _] =>
    apply List.Forall_cons => //=
  | |- e_is_basic (AI_basic ?e) =>
    by unfold e_is_basic; exists e
  end.

(** A common scheme in the progress proof, with a continuation. **)
Ltac solve_progress_cont cont :=
  repeat eexists;
  solve [
      apply r_simple; solve [ eauto | constructor; eauto | cont; eauto ]
    | cont ].

(** The same, but without continuation. **)
Ltac solve_progress :=
  solve_progress_cont ltac:(fail).


(* For proving the numerics in init, copy, and fill instructions *)
Lemma Int32_decrement: forall s s',
  s' = Wasm_int.int_sub i32m s Wasm_int.Int32.one ->
  Z.to_N (Wasm_int.Int32.unsigned s')
    = (Z.to_N (Wasm_int.Int32.unsigned s) - 1)%N.
Proof.
  intros. rewrite H. simpl.
  replace (Wasm_int.Int32.Z_mod_modulus
          (Z.sub (Wasm_int.Int32.unsigned s) 1))
     with (Z.sub (Wasm_int.Int32.unsigned s) 1) => //.
  2: {
    symmetry. eapply Wasm_int.Int32.Z_mod_modulus_id; eauto.
    (* -1 < s1 - 1, since s1 <> 0 and s1 unsigned, so s1 > 0 *)
    (* s1 - 1 < Int32.modulus, since s1 was valid (s1 < Int32.modulus) *)
    admit.
  }
  rewrite Z2N.inj_sub => //.
Admitted.
Lemma Int32_increment: forall s s',
  s' = Wasm_int.int_add i32m s Wasm_int.Int32.one ->
  Z.to_N (Wasm_int.Int32.unsigned s')
    = (Z.to_N (Wasm_int.Int32.unsigned s) + 1)%N.
Proof.
  intros. rewrite H. simpl.
  replace (Wasm_int.Int32.Z_mod_modulus
          (Z.add (Wasm_int.Int32.unsigned s) 1))
     with (Z.add (Wasm_int.Int32.unsigned s) 1) => //.
  2: {
    symmetry. eapply Wasm_int.Int32.Z_mod_modulus_id; eauto.
    (* -1 < s0 + 1, s0 unsigned, so s0 >= 0 *)
    (* s0 + 1 < Int32.modulus, since s0 + s1 <= tab_size t,
        (tab_size t < Int32.modulus)? *)
    admit.
  }
  rewrite Z2N.inj_add => //. admit. (* 0 <= s0, s0 unsigned *)
Admitted.
Lemma Int32_add_decrement: forall s1 s2 s1',
  s1' = Wasm_int.int_sub i32m
        (Wasm_int.int_add i32m s1 s2) Wasm_int.Int32.one ->
  Z.to_N (Wasm_int.Int32.unsigned s1') =
    (Z.to_N (Wasm_int.Int32.unsigned s1) +
    Z.to_N (Wasm_int.Int32.unsigned s2) - 1)%N.
Proof.
  intros. rewrite H. simpl.
  remember (Z.add (Wasm_int.Int32.unsigned s1)
            (Wasm_int.Int32.unsigned s2)) as s.
  replace (Wasm_int.Int32.Z_mod_modulus s) with (s) => //.
  2: {
    rewrite Heqs. symmetry.
    eapply Wasm_int.Int32.Z_mod_modulus_id; eauto.
    (* -1 < s1 + s2, s1 and s2 unsigned, so s1 + s2 >= 0 *)
    (* s1 + s2 < Int32.modulus, since s1 + s2 <= tab_size t,
        (tab_size t < Int32.modulus)? *)
    admit.
  }
Admitted.


Lemma t_progress_be: forall C bes ts1 ts2 vcs lab ret s f hs,
    store_typing s ->
    inst_typing s f.(f_inst) C ->
    be_typing (upd_label (upd_local_label_return C (map typeof f.(f_locs)) (tc_label C) ret) lab) bes (Tf ts1 ts2) ->
    map typeof vcs = ts1 ->
    not_lf_br (to_e_list bes) 0 ->
    not_lf_return (to_e_list bes) 0 ->
    const_list (to_e_list bes) \/
    exists s' f' es' hs', reduce hs s f (v_to_e_list vcs ++ to_e_list bes) hs' s' f' es'.
Proof.
  move => C bes ts1 ts2 vcs lab ret s f hs HST HIT HType HConstType HNBI_br HNRet.
  generalize dependent vcs.
  gen_ind HType; try by left.
  - (* Ref_is_null *)
    right. invert_typeof_vcs.
    destruct v as [| |[]]=> //=; try solve_progress;
    [ replace (AI_ref f0) with (v_to_e (VAL_ref (VAL_ref_func f0)))
    | replace (AI_ref_extern e) with (v_to_e (VAL_ref (VAL_ref_extern e)))];
    repeat eexists; apply r_simple; eapply rs_ref_is_null_false => //=.

  - (* Ref_func *)
    right. invert_typeof_vcs. simpl in *.
    destruct C0 => //=. simpl in H.
    repeat eexists. eapply r_ref_func => //=.

    (* matching of context types *)
    destruct (f_inst f) => //=.
    destruct tc_elem => //=.
    destruct tc_data => //=.
    destruct tc_local => //=.
    destruct tc_label => //=.
    destruct tc_return => //=.
    destruct tc_ref => //=.

  - (* Unop *)
    right. invert_typeof_vcs.
    by destruct v => //=; solve_progress.

  - (* Binop *)
    right. invert_typeof_vcs.
    destruct v, v0 => //=.
    by destruct (app_binop_num op v v0) eqn:HBinary; solve_progress.

  - (* Testop *)
    right.

    (* invert_typeof_vcs *)
    destruct vcs => //=; destruct vcs => //=.
    simpl in H5. inversion H5.
    unfold typeof in H6. destruct v => //=.
    inversion H6. subst. clear H5 H6.

    destruct v => //=; solve_progress.

  - (* Relop_i *)
    right. invert_typeof_vcs.
    by destruct v => //=; destruct v0 => //=; solve_progress.

  - (* Cvtop *)
    right. 

    (* invert_typeof_vcs *)
    destruct vcs => //=; destruct vcs => //=.
    simpl in H6. inversion H6.
    unfold typeof in H7. destruct v => //=.
    inversion H7. subst. clear H6 H7.

    destruct (cvt t1 sx v) eqn:HConvert; destruct v => //=; solve_progress.
  - (* Reinterpret *)
    right.

    (* invert_typeof_vcs *)
    destruct vcs => //=; destruct vcs => //=.
    simpl in H6. inversion H6.
    unfold typeof in H7. destruct v => //=.
    inversion H7. subst. clear H6 H7.

    by destruct v => //=; solve_progress_cont ltac:(apply rs_reinterpret).
    
  - (* Unreachable *)
    right.
    exists s, f, (v_to_e_list vcs ++ [::AI_trap]), hs.
    apply reduce_composition_left; first by apply v_to_e_is_const_list.
    apply r_simple. by constructor.

  - (* Nop *)
    right.
    exists s, f, (v_to_e_list vcs ++ [::]), hs.
    apply reduce_composition_left; first by apply v_to_e_is_const_list.
    apply r_simple. by constructor.

  - (* Drop *)
    right. invert_typeof_vcs. solve_progress.

  - (* Select Some *)
    right. invert_typeof_vcs.
    destruct v1 => //=. destruct v1 => //=.
    destruct (s0 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0;
    solve_progress.
    
  - (* Select None *)
    right. invert_typeof_vcs.
    destruct v1 => //=; destruct v1 => //=;
    destruct v0 => //=; destruct v0 => //=;
    destruct v => //=; destruct v => //=;
    destruct (s0 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0;
    try (fold (v_to_e (VAL_num (VAL_int32 s1))); fold (v_to_e (VAL_num (VAL_int32 s2))));
    try (fold (v_to_e (VAL_num (VAL_int64 s1))); fold (v_to_e (VAL_num (VAL_int64 s2))));
    try (fold (v_to_e (VAL_num (VAL_float32 s1))); fold (v_to_e (VAL_num (VAL_float32 s2))));
    try (fold (v_to_e (VAL_num (VAL_float64 s1))); fold (v_to_e (VAL_num (VAL_float64 s2))));
    try (fold (v_to_e (VAL_vec (VAL_vec128 v))); fold (v_to_e (VAL_vec (VAL_vec128 v0))));
    repeat eexists; apply r_simple; constructor => //=; discriminate.

  - (* Block *)
    right.
    exists s, f, [::AI_label (length tm) [::] (v_to_e_list vcs ++ to_e_list es)], hs.
    eapply r_block with (t1s := ts1) => //=.
    + (* matching of context types *)
      destruct tb => //=; last by rewrite -H3 -H.
      destruct (f_inst f) => //=.
      unfold expand_t in H. destruct C, C0 => //=. simpl in *.
      (* HIT says inst_types = tc_type0 *)
      destruct tc_elem0 => //=.
      destruct tc_data0 => //=.
      destruct tc_local0 => //=.
      destruct tc_label0 => //=.
      destruct tc_return0 => //=.
      destruct tc_ref0 => //=.
      repeat (move/andP in HIT; destruct HIT as [HIT ?]).
      move/eqP in HIT. rewrite HIT.
      (* H0 says tc_type = tc_type0 *)
      unfold upd_label, upd_local_label_return in H0. simpl in H0.
      inversion H0. rewrite H3 H10 in H => //=.
    + by apply v_to_e_is_const_list.
    + repeat rewrite length_is_size. rewrite v_to_e_size.
      subst. by rewrite size_map.
  
  - (* Loop *)
    right.
    exists s, f, [::AI_label (length vcs) [::AI_basic (BI_loop tb es)] (v_to_e_list vcs ++ to_e_list es)], hs.
    eapply rs_loop with (t1s := ts1) (t2s := ts2); eauto; repeat rewrite length_is_size.
    + (* matching of context types *)
      destruct tb => //=; last by rewrite -ETf -H.
      destruct (f_inst f) => //=.
      unfold expand_t in H. destruct C, C0 => //=. simpl in *.
      (* HIT says inst_types = tc_type0 *)
      destruct tc_elem0 => //=.
      destruct tc_data0 => //=.
      destruct tc_local0 => //=.
      destruct tc_label0 => //=.
      destruct tc_return0 => //=.
      destruct tc_ref0 => //=.
      repeat (move/andP in HIT; destruct HIT as [HIT ?]).
      move/eqP in HIT. rewrite HIT.
      (* H0 says tc_type = tc_type0 *)
      unfold upd_label, upd_local_label_return in H0. simpl in H0.
      inversion H0. rewrite H3 H4 H10 in H => //=.
    + by apply v_to_e_is_const_list.
    + by rewrite v_to_e_size.
    + rewrite -HConstType. by rewrite size_map.

  - (* If *)
    right.
    apply typeof_append in HConstType.
    destruct HConstType as [v [Ha [Hb Hc]]].
    rewrite Ha. rewrite -v_to_e_cat.
    rewrite -catA.
    destruct v => //=. destruct v => //=.
    remember (v_to_e_list (take (size tn) vcs)) as vs.
    assert (size tn < size vcs) as Hsize => //=.
    {
      rewrite Ha -Hb => //=. rewrite size_map. rewrite size_take.
      destruct (size tn < size vcs) eqn:E => //=;
      rewrite size_cat; rewrite size_take => //=;
      [rewrite E | rewrite ltnn]; lias.
    }
    destruct (s0 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
    + exists s, f, [::AI_label (size tm) [::] (vs ++ to_e_list es2)], hs.
      eapply rs_if_false with (t1s := tn) (t2s := tm) => //=.
      * (* matching of context types *)
        destruct tb => //=. destruct (f_inst f) => //=.
        unfold expand_t in H. destruct C, C0 => //=. simpl in *.
        (* HIT says inst_types = tc_type0 *)
        destruct tc_elem0 => //=.
        destruct tc_data0 => //=.
        destruct tc_local0 => //=.
        destruct tc_label0 => //=.
        destruct tc_return0 => //=.
        destruct tc_ref0 => //=.
        repeat (move/andP in HIT; destruct HIT as [HIT ?]).
        move/eqP in HIT. rewrite HIT.
        (* H0 says tc_type = tc_type0 *)
        unfold upd_label, upd_local_label_return in H0. simpl in H0.
        inversion H0. rewrite H10 in H => //=.
      * rewrite Heqvs. by apply v_to_e_is_const_list.
      * repeat rewrite length_is_size. rewrite Heqvs.
        rewrite v_to_e_size. rewrite size_take => //=.
        by rewrite Hsize.
    + exists s, f, [::AI_label (size tm) [::] (vs ++ to_e_list es1)], hs.
      eapply rs_if_true with (t1s := tn) (t2s := tm) => //=.
      * (* matching of context types *)
        destruct tb => //=. destruct (f_inst f) => //=.
        unfold expand_t in H. destruct C, C0 => //=. simpl in *.
        (* HIT says inst_types = tc_type0 *)
        destruct tc_elem0 => //=.
        destruct tc_data0 => //=.
        destruct tc_local0 => //=.
        destruct tc_label0 => //=.
        destruct tc_return0 => //=.
        destruct tc_ref0 => //=.
        repeat (move/andP in HIT; destruct HIT as [HIT ?]).
        move/eqP in HIT. rewrite HIT.
        (* H0 says tc_type = tc_type0 *)
        unfold upd_label, upd_local_label_return in H0. simpl in H0.
        inversion H0. rewrite H10 in H => //=.
      * rewrite Heqvs. by apply v_to_e_is_const_list.
      * repeat rewrite length_is_size. rewrite Heqvs.
        rewrite v_to_e_size. rewrite size_take => //=.
        by rewrite Hsize.

  - (* BI_br *)
    subst.
    exfalso.
    unfold not_lf_br in HNBI_br.
    apply (HNBI_br i (LH_base [::] [::])).
    by apply lfilled0_empty.

  - (* BI_br_if *)
    right.
    apply typeof_append in HConstType.
    destruct HConstType as [v [Ha [Hb Hc]]].
    rewrite Ha. rewrite -v_to_e_cat.
    rewrite -catA.
    destruct v => //=. destruct v => //=.
    destruct (s0 == Wasm_int.int_zero i32m) eqn:Heq0; move/eqP in Heq0.
    + exists s, f, (v_to_e_list (take (size ts2) vcs) ++ [::]), hs.
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_simple; eauto.
    + exists s, f, (v_to_e_list (take (size ts2) vcs) ++ [::AI_basic (BI_br i)]), hs.
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_simple; eauto.

  - (* BI_br_table *)
    right.
    apply cat_split in HConstType. destruct HConstType.
    assert (Evcs : vcs = take (size t1s) vcs ++ drop (size t1s) vcs); first by rewrite cat_take_drop.
    rewrite Evcs.
    symmetry in H6. rewrite -map_drop in H6. apply typeof_append in H6.
    destruct H6 as [v [Ha [Hb Hc]]].
    destruct v => //=. destruct v => //=.
    rewrite Ha.
    repeat rewrite -v_to_e_cat.
    repeat rewrite -catA. rewrite catA.
    destruct (length ins > Wasm_int.nat_of_uint i32m s0) eqn:HLength; move/ltP in HLength.
    + remember HLength as H8. clear HeqH8.
      apply List.nth_error_Some in H8.
      destruct (List.nth_error ins (Wasm_int.nat_of_uint i32m s0)) eqn:HN => //=.
      exists s, f, ((v_to_e_list (take (size t1s) vcs) ++ v_to_e_list (take (size ts) (drop (size t1s) vcs))) ++ [::AI_basic (BI_br n)]), hs.
      apply reduce_composition_left.
      { by apply const_list_concat; apply v_to_e_is_const_list. }
      apply r_simple. apply rs_br_table => //.
      by lias.
    + assert (Inf : length ins <= Wasm_int.nat_of_uint i32m s0); first by lias.
      move/leP in Inf.
      remember Inf as Inf'. clear HeqInf'.
      apply List.nth_error_None in Inf.
      exists s, f, ((v_to_e_list (take (size t1s) vcs) ++ v_to_e_list (take (size ts) (drop (size t1s) vcs))) ++ [::AI_basic (BI_br i)]), hs.
      apply reduce_composition_left.
      { by apply const_list_concat; apply v_to_e_is_const_list. }
      apply r_simple. apply rs_br_table_length => //.
      by lias.

  - (* Return *)
    subst.
    exfalso.
    unfold not_lf_return in HNRet.
    apply (HNRet (LH_base [::] [::])).
    by apply lfilled0_empty.

  - (* Call *)
    right. subst.
    simpl in *. clear H1 H2 H3.
    eapply func_context_store in H; eauto.
    + destruct H as [a H].
      exists s, f, (v_to_e_list vcs ++ [:: (AI_invoke a)]), hs.
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_call => //.
    + eapply lookup_N_Some. by rewrite H.

  - (* Call_indirect *)
    right.
    simpl in *.
    apply typeof_append in HConstType. destruct HConstType as [v [Ha [Hb Hc]]].
    destruct v => //=. destruct v => //=.

    (* need some way of using typing to assert no extern_ref *)
    (* this requires linking the asserted context table with the store table
        and the tableinst_elem type with its tableinst_type *)

    (* stab_elem destruct breakdown to be able to use internal tab *)
    (* destruct (lookup_N (inst_tables (f_inst f)) x) as [tabaddr|] eqn:Etest0 => //=.
    destruct (lookup_N (s_tables s) tabaddr) as [tab|] eqn:Etest1 => //=.
    destruct (List.nth_error (tableinst_elem tab)
        (Z.to_nat (Wasm_int.Int32.unsigned s0))) as [a|] eqn:Etest2 => //=.
        assert (forall ta ti tty,
          lookup_N (inst_tables (f_inst f)) x = Some ta ->
          lookup_N (s_tables s) ta = Some ti ->
          lookup_N (tc_table C) x = Some tty ->
          tableinst_type ti = tty). admit.
        destruct (H4 tabaddr tab tabtype) => //=.
    
    destruct (tableinst_elem tab) eqn:Etin => //=.
    admit. (* nth_error [::] _ = Some *)
    assert (tt_elem_type (tableinst_type tab) = typeof_ref v).
    apply table_val_type_rect with (tail := l) => //=.
    rewrite -Etin in Etest2. rewrite H0 in H8.
    destruct v eqn:Ev => //=. destruct r.
    simpl in *. destruct a eqn:Ea => //=. *)


    rewrite Ha. rewrite -v_to_e_cat. rewrite -catA. subst.
    exists s, f.
    (* destruct (tt_elem_type (tableinst_type tab)) eqn:Etabt => //=.
    simpl in H. destruct a => //=. simpl in *. discriminate. 2:{} *)

    destruct (stab_elem s f.(f_inst) x (Wasm_int.nat_of_uint i32m s0)) as [a|] eqn:Hstabaddr.
    + (* Some a *)
      clear H2 Hc. simpl in *.
      (* unfold stab_elem, stab in Hstabaddr. simpl in *.
      destruct C0 => //=. simpl in *. *)
      (* inst_tables -> tableaddr -> s_tables -> tableinst -> tableinst_elem -> value_ref *)
      (* try to assert instance has it if the store has it -> store_typing_stabaddr *)
      (* unfold stab_elem, stab in Hstabaddr. simpl in *.
      destruct C0 => //=. simpl in *.
      destruct (f_inst f) => //=. simpl in *.
      destruct tc_elem, tc_data, tc_local, tc_label, tc_return, tc_ref => //=.
      do 4! (move/andP in HIT; destruct HIT as [HIT ?]).
      unfold lookup_N in *.
      tabtype
      inst_tables
      eapply all2_projection with (f0 := (tabi_agree (s_tables s)))
        (l1 := inst_tables) (l2 := tc_table) (n := N.to_nat x)
        (x1 := a) (x2 := tabtype) in H4 => //=.
      unfold tabi_agree, option_map, tab_typing in H4. *)
      
      unfold inst_tables in Hstabaddr.
      remember Hstabaddr as Hstabaddr2. clear HeqHstabaddr2.
      destruct a eqn:Ea => //=.
      * exists ((v_to_e_list (take (size t1s) vcs)) ++ [:: AI_trap]), hs.
        apply reduce_composition_left; first by apply v_to_e_is_const_list.
        eapply r_call_indirect_failure4; eauto.
      * eapply store_typing_stabaddr in Hstabaddr; eauto.
        destruct Hstabaddr as [cl Hstabaddr].
        destruct (stypes s f.(f_inst) (N.to_nat y) == Some (cl_type cl)) eqn:Hclt; move/eqP in Hclt.
        -- exists (v_to_e_list (take (size t1s) vcs) ++ [::AI_invoke f0]), hs.
          apply reduce_composition_left; first by apply v_to_e_is_const_list.
          eapply r_call_indirect_success; eauto.
        -- exists (v_to_e_list (take (size t1s) vcs) ++ [::AI_trap]), hs.
          apply reduce_composition_left; first by apply v_to_e_is_const_list.
          by eapply r_call_indirect_failure1; eauto.
      * (* ref_extern *)
        clear ETf H3.
        unfold stab_elem, stab in Hstabaddr.
        remove_bools_options.
        
        remember HIT as HIT'. clear HeqHIT'.
        eapply inst_typing_tab_ttype in HIT; eauto.
        eapply store_typing_tabv_type in HST; eauto.
        rewrite HIT in HST. rewrite HST in H0 => //=.

    + (* None *)
      exists (v_to_e_list (take (size t1s) vcs) ++ [::AI_trap]), hs.
      apply reduce_composition_left; first by apply v_to_e_is_const_list.
      by apply r_call_indirect_failure3.
    
  - (* Local_get *)
    right. invert_typeof_vcs.
    simpl in H. unfold lookup_N in H. clear H0.
    apply nth_error_map in H.
    destruct H as [x' [HN HType]].
    exists s, f, [:: v_to_e x'], hs.
    by apply r_local_get.
      
  - (* Local_set *)
    right. invert_typeof_vcs. simpl in H.
    assert (lookup_N [seq typeof i | i <- f_locs f] x <> None) as H'; 
    first by rewrite H. apply lookup_N_Some in H'.
    rewrite length_is_size in H'. rewrite size_map in H'.
    exists s, (Build_frame (set_nth v f.(f_locs) (N.to_nat x) v) f.(f_inst)), [::], hs.
    eapply r_local_set with (vd := v); eauto.

  - (* Local_tee *)
    right. invert_typeof_vcs.
    exists s, f, [:: v_to_e v; v_to_e v; AI_basic (BI_local_set x)], hs.
    apply r_simple. apply rs_local_tee.
    destruct v => //=. destruct v => //=.

  - (* Global_get *)
    right. invert_typeof_vcs.
    simpl in H. clear H0.
    unfold option_map in H.
    destruct (List.nth_error (tc_global C0) (N.to_nat x)) eqn:HN => //=;
    last by (unfold lookup_N in H; rewrite HN in H).
    eapply glob_context_store in HN; eauto.
    2: {
      assert (List.nth_error (tc_global C0) (N.to_nat x) <> None);
      first by rewrite HN. apply List.nth_error_Some in H0.
      by move/ltP in H0.
    }
    assert (D : sglob_val s f.(f_inst) (N.to_nat x) <> None).
    { unfold sglob_val. unfold sglob in HN. unfold option_map.
    by destruct (operations.sglob s f.(f_inst) (N.to_nat x)). }
    destruct (sglob_val s f.(f_inst) (N.to_nat x)) eqn:Hglobval => //=.
    exists s, f, [:: v_to_e v], hs.
    by apply r_global_get.

  - (* Global_set *)
    right. invert_typeof_vcs.
    destruct (supdate_glob s f.(f_inst) (N.to_nat x) v) eqn:Hs.
    + exists s0, f, [::], hs.
      by apply r_global_set.
    + unfold supdate_glob in Hs. unfold option_bind in Hs.
      simpl in H. unfold lookup_N in H.
      eapply glob_context_store in H; eauto.
      2: {
        assert (List.nth_error (tc_global C0) (N.to_nat x) <> None);
        first by rewrite H. apply List.nth_error_Some in H0.
        by move/ltP in H0.
      }
      unfold sglob in H. unfold operations.sglob in H. unfold option_bind in H.
      destruct (sglob_ind s f.(f_inst) (N.to_nat x)) eqn:Hglob => //.
      unfold supdate_glob_s in Hs. unfold option_map in Hs.
      destruct (lookup_N (s_globals s) g0) => //.

  - (* Table_get *)
    right. invert_typeof_vcs.
    simpl in H. clear H1 H2 ETf.
    destruct v as [[]| |] => //=.
    destruct (stab_elem s f.(f_inst) x (Wasm_int.nat_of_uint i32m s0)) eqn:Ev.
    + exists s, f, [::v_to_e (VAL_ref v)], hs.
      by apply r_table_get_success.
    + exists s, f, [::AI_trap], hs.
      by apply r_table_get_failure.

  - (* Table_set *)
    right. invert_typeof_vcs.
    simpl in *. clear H1 H2 ETf.
    (* same as using HIT:inst_typing to get [tabtype] using
        "lookup_N (s_tables s)"@ "inst_tables (f_inst f)"@ x *)
    (* then matching with H:lookup (tc_table C0) x to get [s'] using
        "s_tables := set_nth tab (s_tables s) (N.to_nat x) tab" *)
    destruct v as [[]| |], v0 => //=.
    destruct (stab_update s f.(f_inst) x (Wasm_int.nat_of_uint i32m s0) v) eqn:Es.
    + unfold stab_update, stab in Es.
      exists s1, f, [::], hs.
      apply r_table_set_success. apply Es.
    + exists s, f, [::], hs.
      by apply r_table_set_failure.
  
  - (* Table_size *)
    right. invert_typeof_vcs.
    simpl in *. clear H0 H1 HConstType ETf.

    assert (exists t, stab s f.(f_inst) x = Some t) as Ht.
    {
      remember HIT as HIT'. clear HeqHIT'.
      eapply inst_index_get_instval_tab in HIT'; eauto.
      destruct HIT' as [a Ha].

      unfold stab.
      unfold inst_typing, typing.inst_typing in HIT.
      destruct C0, (f_inst f), tc_elem, tc_data,
              tc_local, tc_label, tc_return, tc_ref => //.
      remove_bools_options.
      simpl in H. unfold tabi_agree in H2.
      eapply all2_projection in H2; eauto.
      simpl in *. unfold lookup_N.
      remove_bools_options. rewrite Ha; eauto.
    }
    destruct Ht as [t Ht].
    
    exists s, f, [:: $VAN VAL_int32
            (Wasm_int.int_of_Z i32m (Z.of_nat (tab_size t)))], hs.
    eapply r_table_size with (tab := t) => //=.
  
  - (* Table_grow *)
    right. invert_typeof_vcs.
    simpl in *. destruct v => //=. destruct v0 as [[]| |] => //=.
    clear H1 H8 ETf HConstType.

    assert (exists t, stab s f.(f_inst) x = Some t) as Ht.
    {
      remember HIT as HIT'. clear HeqHIT'.
      eapply inst_index_get_instval_tab in HIT'; eauto.
      destruct HIT' as [a Ha].

      unfold stab.
      unfold inst_typing, typing.inst_typing in HIT.
      destruct C0, (f_inst f), tc_elem, tc_data,
              tc_local, tc_label, tc_return, tc_ref => //.
      remove_bools_options.
      simpl in H. unfold tabi_agree in H3.
      eapply all2_projection in H3; eauto.
      simpl in *. unfold lookup_N.
      remove_bools_options. rewrite Ha; eauto.
    }
    destruct Ht as [t Ht].

    destruct (stab_grow s (f_inst f) x (Wasm_int.N_of_uint i32m s0) v) eqn:Etabg.
    + exists s1, f, [:: $VAN VAL_int32
          (Wasm_int.int_of_Z i32m (Z.of_nat (tab_size t)))], hs.
      apply r_table_grow_success with (tab := t) => //=.
    + exists s, f, [:: $VAN VAL_int32 int32_minus_one], hs.
      destruct (tab_size t) eqn:Etabs.
      * apply r_table_grow_failure with (tab := t) (sz := 0) => //=.
      * apply r_table_grow_failure with (tab := t) (sz := n.+1) => //=.
  
  - (* Table_fill *)
    right. invert_typeof_vcs. simpl in *.
    destruct v as [[]| |], v0, v1 as [[]| |] => //=.
    clear H1 H2 ETf HConstType.
    
    assert (exists t, stab s f.(f_inst) x = Some t) as Ht.
    {
      remember HIT as HIT'. clear HeqHIT'.
      eapply inst_index_get_instval_tab in HIT'; eauto.
      destruct HIT' as [a Ha].

      unfold stab.
      unfold inst_typing, typing.inst_typing in HIT.
      destruct C0, (f_inst f), tc_elem, tc_data,
              tc_local, tc_label, tc_return, tc_ref => //.
      remove_bools_options.
      simpl in H. unfold tabi_agree in H2.
      eapply all2_projection in H2; eauto.
      simpl in *. unfold lookup_N.
      remove_bools_options. rewrite Ha; eauto.
    }
    destruct Ht as [t Ht].

    destruct (tab_size t >= Wasm_int.nat_of_uint i32m s0 + Wasm_int.nat_of_uint i32m s1) eqn:Etabs.
    + destruct (s1 == Wasm_int.int_zero i32m) eqn:En; move/eqP in En.
      * exists s, f, [::], hs.
        apply r_table_fill_return with (tab := t) => //=.
      * (* destruct s0 eqn:Es0. destruct s1 eqn:Es1. simpl in *. unfold Wasm_int.int_zero in En. *)
        remember (Wasm_int.int_add i32m s0 Wasm_int.Int32.one) as s0'.
        remember (Wasm_int.int_sub i32m s1 Wasm_int.Int32.one) as s1'.
        exists s, f, [:: $VAN VAL_int32 s0; v_to_e (VAL_ref v);
            AI_basic (BI_table_set x); $VAN VAL_int32 s0';
            v_to_e (VAL_ref v); $VAN VAL_int32 s1';
            AI_basic (BI_table_fill x)], hs.
        apply r_table_fill_step with (tab := t) => //=.
        -- apply Int32_decrement => //=.
        -- apply Int32_increment => //=.
    + exists s, f, [:: AI_trap], hs.
      apply r_table_fill_bound with (tab := t) => //=.
      move/negP in Etabs. move/negP in Etabs.
      rewrite -ltnNge in Etabs. by rewrite Etabs.

  - (* Table_copy *)
    right. invert_typeof_vcs. simpl in *.
    destruct v as [[]| |], v0 as [[]| |], v1 as [[]| |] => //=.
    clear ETf HConstType H3.

    assert (exists t, stab s f.(f_inst) x = Some t) as Ht.
    {
      remember HIT as HIT'. clear HeqHIT'.
      eapply inst_index_get_instval_tab in HIT'; eauto.
      destruct HIT' as [a Ha].

      unfold stab.
      unfold inst_typing, typing.inst_typing in HIT.
      destruct C0, (f_inst f), tc_elem, tc_data,
              tc_local, tc_label, tc_return, tc_ref => //.
      remove_bools_options.
      simpl in H. unfold tabi_agree in H5.
      eapply all2_projection in H5; eauto.
      simpl in *. unfold lookup_N.
      remove_bools_options. rewrite Ha; eauto.
    }
    destruct Ht as [tx Htx].

    assert (exists t, stab s f.(f_inst) y = Some t) as Ht.
    {
      remember HIT as HIT'. clear HeqHIT'.
      eapply inst_index_get_instval_tab
        with (j := (N.to_nat y)) in HIT'; eauto.
      destruct HIT' as [a Ha].

      unfold stab.
      unfold inst_typing, typing.inst_typing in HIT.
      destruct C0, (f_inst f), tc_elem, tc_data,
              tc_local, tc_label, tc_return, tc_ref => //.
      remove_bools_options.
      simpl in H. unfold tabi_agree in H5.
      eapply all2_projection in H5; eauto.
      simpl in *. unfold lookup_N.
      remove_bools_options. rewrite Ha; eauto.
    }
    destruct Ht as [ty Hty].

    destruct (tab_size tx >= Wasm_int.nat_of_uint i32m s0 + Wasm_int.nat_of_uint i32m s2) eqn:Etabsx;
    destruct (tab_size ty >= Wasm_int.nat_of_uint i32m s1 + Wasm_int.nat_of_uint i32m s2) eqn:Etabsy.
    + destruct (s2 == Wasm_int.int_zero i32m) eqn:En; move/eqP in En.
      * exists s, f, [::], hs.
        apply r_table_copy_return with (tabx := tx) (taby := ty) => //=.
      * destruct (Wasm_int.N_of_uint i32m s0 <= Wasm_int.N_of_uint i32m s1) eqn:Emode.
        -- (* forward *)
          remember (Wasm_int.int_add i32m s0 Wasm_int.Int32.one) as s0'.
          remember (Wasm_int.int_add i32m s1 Wasm_int.Int32.one) as s1'.
          remember (Wasm_int.int_sub i32m s2 Wasm_int.Int32.one) as s2'.
          exists s, f, [:: $VAN VAL_int32 s0; $VAN VAL_int32 s1;
            AI_basic (BI_table_get y); AI_basic (BI_table_set x);
            $VAN VAL_int32 s0'; $VAN VAL_int32 s1'; $VAN VAL_int32 s2';
            AI_basic (BI_table_copy x y)], hs.
          apply r_table_copy_forward
            with (tabx := tx) (taby := ty) => //=.
          ++ apply Int32_decrement => //=.
          ++ apply Int32_increment => //=.
          ++ apply Int32_increment => //=.
        -- (* backward *)
          remember (Wasm_int.int_sub i32m (Wasm_int.int_add i32m s0 s2)
                      Wasm_int.Int32.one) as s0'.
          remember (Wasm_int.int_sub i32m (Wasm_int.int_add i32m s1 s2)
                      Wasm_int.Int32.one) as s1'.
          remember (Wasm_int.int_add i32m s2 Wasm_int.Int32.one) as s2'.
          exists s, f, [:: $VAN VAL_int32 s0'; $VAN VAL_int32 s1';
            AI_basic (BI_table_get y); AI_basic (BI_table_set x);
            $VAN VAL_int32 s0; $VAN VAL_int32 s1; $VAN VAL_int32 s2';
            AI_basic (BI_table_copy x y)], hs.
          apply r_table_copy_backward
            with (tabx := tx) (taby := ty) => //=.
          move/negP in Emode. move/negP in Emode.
          rewrite -ltnNge in Emode. by rewrite Emode.
          ++ apply Int32_increment => //=.
          ++ apply Int32_add_decrement => //=.
          ++ apply Int32_add_decrement => //=.
    + exists s, f, [:: AI_trap], hs.
      apply r_table_copy_bound with (tabx := tx) (taby := ty) => //=.
      left. move/negP in Etabsy. move/negP in Etabsy.
      rewrite -ltnNge in Etabsy. by rewrite Etabsy.
    + exists s, f, [:: AI_trap], hs.
      apply r_table_copy_bound with (tabx := tx) (taby := ty) => //=.
      right. move/negP in Etabsx. move/negP in Etabsx.
      rewrite -ltnNge in Etabsx. by rewrite Etabsx.
    + exists s, f, [:: AI_trap], hs.
      apply r_table_copy_bound with (tabx := tx) (taby := ty) => //=.
      right. move/negP in Etabsx. move/negP in Etabsx.
      rewrite -ltnNge in Etabsx. by rewrite Etabsx.
  
  - (* Table_init *)
    right. invert_typeof_vcs. simpl in *.
    destruct v as [[]| |], v0 as [[]| |], v1 as [[]| |] => //=.
    clear ETf HConstType H3.

    assert (exists t, stab s f.(f_inst) x = Some t) as Ht.
    {
      remember HIT as HIT'. clear HeqHIT'.
      eapply inst_index_get_instval_tab in HIT'; eauto.
      destruct HIT' as [a Ha].

      unfold stab.
      unfold inst_typing, typing.inst_typing in HIT.
      destruct C0, (f_inst f), tc_elem, tc_data,
              tc_local, tc_label, tc_return, tc_ref => //.
      remove_bools_options.
      simpl in H. unfold tabi_agree in H4.
      eapply all2_projection in H4; eauto.
      simpl in *. unfold lookup_N.
      remove_bools_options. rewrite Ha; eauto.
    }
    destruct Ht as [t Ht].

    assert (exists e, selem s f.(f_inst) y = Some e) as He.
    {
      admit. 
      (* elem here, not table *)

      (* remember HIT as HIT'. clear HeqHIT'.
      eapply inst_index_get_instval_tab
        with (j := (N.to_nat y)) in HIT'; eauto.
      destruct HIT' as [a Ha].

      unfold stab.
      unfold inst_typing, typing.inst_typing in HIT.
      destruct C0, (f_inst f), tc_elem, tc_data,
              tc_local, tc_label, tc_return, tc_ref => //.
      remove_bools_options.
      simpl in H. unfold tabi_agree in H4.
      eapply all2_projection in H4; eauto.
      simpl in *. unfold lookup_N.
      remove_bools_options. rewrite Ha; eauto. *)
    }
    destruct He as [e He].

    destruct (tab_size t >= Wasm_int.nat_of_uint i32m s0 + Wasm_int.nat_of_uint i32m s2) eqn:Etabs;
    destruct (elem_size e >= Wasm_int.nat_of_uint i32m s1 + Wasm_int.nat_of_uint i32m s2) eqn:Eelems.
    + destruct (s2 == Wasm_int.int_zero i32m) eqn:En; move/eqP in En.
      * exists s, f, [::], hs.
        apply r_table_init_return with (tab := t) (elem := e) => //=.
      * destruct (lookup_N (eleminst_elem e) (Wasm_int.N_of_uint i32m s1)) eqn:Eeleml.
        -- remember (Wasm_int.int_add i32m s0 Wasm_int.Int32.one) as s0'.
          remember (Wasm_int.int_add i32m s1 Wasm_int.Int32.one) as s1'.
          remember (Wasm_int.int_sub i32m s2 Wasm_int.Int32.one) as s2'.
          exists s, f, [:: $VAN VAL_int32 s0; v_to_e (VAL_ref v);
              AI_basic (BI_table_set x); $VAN VAL_int32 s0';
              $VAN VAL_int32 s1'; $VAN VAL_int32 s2';
              AI_basic (BI_table_init x y)], hs.
          apply r_table_init_step with (tab := t) (elem := e) => //=.
          ++ apply Int32_decrement => //=.
          ++ apply Int32_increment => //=.
          ++ apply Int32_increment => //=.
        -- admit. (* fix using above, this is impossible *)
    + exists s, f, [:: AI_trap], hs.
      apply r_table_init_bound with (tab := t) (elem := e) => //=.
      left. move/negP in Eelems. move/negP in Eelems.
      rewrite -ltnNge in Eelems. by rewrite Eelems.
    + exists s, f, [:: AI_trap], hs.
      apply r_table_init_bound with (tab := t) (elem := e) => //=.
      right. move/negP in Etabs. move/negP in Etabs.
      rewrite -ltnNge in Etabs. by rewrite Etabs.
    + exists s, f, [:: AI_trap], hs.
      apply r_table_init_bound with (tab := t) (elem := e) => //=.
      right. move/negP in Etabs. move/negP in Etabs.
      rewrite -ltnNge in Etabs. by rewrite Etabs.
  
  - (* Elem_drop *)
    right. invert_typeof_vcs. simpl in *.
    clear H0 H1 ETf HConstType.
    (* same as using HIT:inst_typing to get [tt_elem_type tabtype] using
        "lookup_N (s_elems s)"@ "inst_elems (f_inst f)"@ x *)
    (* then matching with H:lookup (tc_elem C0) x to get [s'] using
        "s_elems := set_nth elem (s_elems s) (N.to_nat x) elem" *)
    destruct (selem_drop s f.(f_inst) x) eqn:Eelem.
    + unfold selem_drop in Eelem.
      (* remove_bools_options. *)
      exists s0, f, [::], hs.
      apply r_elem_drop => //=.
    + admit. (* fix using above, this is impossible *)
  
  - (* Load *)
    right. subst.
    simpl in H.
    exists s, f.
    invert_typeof_vcs. destruct v => //=. destruct v => //=.
    eapply mem_context_store in H; eauto.
    destruct H as [n [HMenInd HMem]].
    destruct (List.nth_error (s_mems s) (N.to_nat n)) eqn:HN => //=.
    destruct tp_sx.
    + (* Load Packed *)
      destruct p as [tp sx].
      simpl in H0. remove_bools_options.
      destruct (load_packed sx m (Wasm_int.N_of_uint i32m s0) off (tp_length tp) (tnum_length t)) eqn:HLoadResult.
      * exists [::$VAN (wasm_deserialise b t)], hs.
        by eapply r_load_packed_success; eauto.
      * exists [::AI_trap], hs.
        by eapply r_load_packed_failure; eauto.
    + (* Load *)
      simpl in H0.
      destruct (load m (Wasm_int.N_of_uint i32m s0) off (tnum_length t)) eqn:HLoadResult.
      * exists [::$VAN (wasm_deserialise b t)], hs.
        by eapply r_load_success; eauto.
      * exists [::AI_trap], hs.
        by eapply r_load_failure; eauto.

  - (* Store *)
    right. subst.
    simpl in H.
    invert_typeof_vcs. destruct v, v0 => //=. destruct v => //=.
    eapply mem_context_store in H; eauto.
    destruct H as [n [HMenInd HMem]].
    destruct (List.nth_error (s_mems s) (N.to_nat n)) eqn:HN => //=.
    destruct tp as [tp |].
    + (* Store Packed *)
      simpl in H0. remove_bools_options.
      destruct (store_packed m (Wasm_int.N_of_uint i32m s0) off (bits v0) (tp_length tp)) eqn:HStoreResult.
      * exists (upd_s_mem s (set_nth m0 s.(s_mems) (N.to_nat n) m0)), f, [::], hs.
        eapply r_store_packed_success; eauto.
        unfold typeof in H5. by inversion H5.
      * exists s, f, [::AI_trap], hs.
        eapply r_store_packed_failure; eauto.
        unfold typeof in H5. by inversion H5.
    + (* Store *)
      simpl in H0.
      destruct (store m (Wasm_int.N_of_uint i32m s0) off (bits v0) (tnum_length (t))) eqn:HStoreResult.
      * exists (upd_s_mem s (set_nth m0 s.(s_mems) (N.to_nat n) m0)), f, [::], hs.
        eapply r_store_success; eauto.
        unfold typeof in H5. by inversion H5.
      * exists s, f, [::AI_trap], hs.
        eapply r_store_failure; eauto.
        unfold typeof in H5. by inversion H5.

  - (* Memory_size *)
    right. invert_typeof_vcs.
    simpl in H.
    eapply mem_context_store in H; eauto.
    destruct H as [n [HMemInd HMem]].
    destruct (List.nth_error (s_mems s) (N.to_nat n)) eqn:HN => //=.
    exists s, f, [:: $VAN (VAL_int32 (Wasm_int.int_of_Z i32m (Z.of_nat (mem_size m))))], hs.
    by eapply r_memory_size; eauto.

  - (* Memory_grow *)
    right. invert_typeof_vcs.
    simpl in H.
    eapply mem_context_store in H; eauto.
    destruct H as [n [HMemInd HMem]].
    destruct (List.nth_error (s_mems s) (N.to_nat n)) eqn:HN => //=.
    destruct v => //=. destruct v => //=.
    (* Similarly, for this proof we can just use trap and use the failure case. *)
    exists s, f, [:: $VAN (VAL_int32 int32_minus_one)], hs.
    by eapply r_memory_grow_failure; eauto.

  - (* Memory_fill *)
    right. invert_typeof_vcs. simpl in *.
    destruct v as [[]| |], v0 as [[]| |], v1 as [[]| |] => //=.
    clear H0 H1 ETf HConstType.

    assert (exists mem, smem s f.(f_inst) = Some mem) as Hmem.
    {
      unfold smem.
      assert (size (tc_memory C0) > 0);
        first by destruct C0, tc_memory => //=.
      
      assert (size (inst_mems (f_inst f)) > 0);
        first by unfold inst_typing, typing.inst_typing in HIT;
        destruct C0, (f_inst f), tc_elem, tc_data,
                tc_local, tc_label, tc_return, tc_ref => //;
        remove_bools_options; rewrite all2E in H2;
        remove_bools_options; rewrite H2 => //=.

      destruct (inst_mems (f_inst f)) eqn:Einst => //=.
      assert (List.nth_error (inst_mems (f_inst f)) 0 = Some m);
        first by rewrite Einst.
      
      remember HIT as HIT'. clear HeqHIT'.
      eapply inst_index_get_contextval_mem in HIT'; eauto.
      destruct HIT' as [a Ha].

      eapply inst_typing_mem in HIT; eauto.
    }
    destruct Hmem as [mem Hmem].

    destruct (mem_length mem >= Wasm_int.N_of_uint i32m s0 + Wasm_int.N_of_uint i32m s2) eqn:Etabs.
    + destruct (s2 == Wasm_int.int_zero i32m) eqn:En; move/eqP in En.
      * exists s, f, [::], hs.
        apply r_memory_fill_return with (mem := mem) => //=.
      * remember (Wasm_int.int_add i32m s0 Wasm_int.Int32.one) as s0'.
        remember (Wasm_int.int_sub i32m s2 Wasm_int.Int32.one) as s2'.
        exists s, f, [:: $VAN VAL_int32 s0; $VAN VAL_int32 s1;
            AI_basic (BI_store T_i32 (Some Tp_i8) 0%N 0%N);
            $VAN VAL_int32 s0'; $VAN VAL_int32 s1; $VAN VAL_int32 s2';
            AI_basic BI_memory_fill], hs.
        apply r_memory_fill_step with (mem := mem) => //=.
        -- apply Int32_decrement => //=.
        -- apply Int32_increment => //=.
    + exists s, f, [:: AI_trap], hs.
      apply r_memory_fill_bound with (mem := mem) => //=.
      move/negP in Etabs. move/negP in Etabs.
      rewrite -ltnNge in Etabs. by rewrite Etabs.

  - (* Memory_copy *)
    right. invert_typeof_vcs. simpl in *.
    destruct v as [[]| |], v0 as [[]| |], v1 as [[]| |] => //=.
    clear H0 H1 ETf HConstType.

    assert (exists mem, smem s f.(f_inst) = Some mem) as Hmem.
    {
      unfold smem.
      assert (size (tc_memory C0) > 0);
        first by destruct C0, tc_memory => //=.
      
      assert (size (inst_mems (f_inst f)) > 0);
        first by unfold inst_typing, typing.inst_typing in HIT;
        destruct C0, (f_inst f), tc_elem, tc_data,
                tc_local, tc_label, tc_return, tc_ref => //;
        remove_bools_options; rewrite all2E in H2;
        remove_bools_options; rewrite H2 => //=.

      destruct (inst_mems (f_inst f)) eqn:Einst => //=.
      assert (List.nth_error (inst_mems (f_inst f)) 0 = Some m);
        first by rewrite Einst.
      
      remember HIT as HIT'. clear HeqHIT'.
      eapply inst_index_get_contextval_mem in HIT'; eauto.
      destruct HIT' as [a Ha].

      eapply inst_typing_mem in HIT; eauto.
    }
    destruct Hmem as [mem Hmem].
    
    destruct (mem_length mem >= Wasm_int.N_of_uint i32m s0 + Wasm_int.N_of_uint i32m s2) eqn:Ememsd;
    destruct (mem_length mem >= Wasm_int.N_of_uint i32m s1 + Wasm_int.N_of_uint i32m s2) eqn:Ememss.
    + destruct (s2 == Wasm_int.int_zero i32m) eqn:En; move/eqP in En.
      * exists s, f, [::], hs.
        apply r_memory_copy_return with (mem := mem) => //=.
      * destruct (Wasm_int.N_of_uint i32m s0 <= Wasm_int.N_of_uint i32m s1) eqn:Emode.
        -- (* forward *)
          remember (Wasm_int.int_add i32m s0 Wasm_int.Int32.one) as s0'.
          remember (Wasm_int.int_add i32m s1 Wasm_int.Int32.one) as s1'.
          remember (Wasm_int.int_sub i32m s2 Wasm_int.Int32.one) as s2'.
          exists s, f, [:: $VAN VAL_int32 s0; $VAN VAL_int32 s1;
            AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) 0%N 0%N);
            AI_basic (BI_store T_i32 (Some Tp_i8) 0%N 0%N);
            $VAN VAL_int32 s0'; $VAN VAL_int32 s1'; $VAN VAL_int32 s2';
            AI_basic BI_memory_copy], hs.
          apply r_memory_copy_forward with (mem := mem) => //=.
          ++ apply Int32_decrement => //=.
          ++ apply Int32_increment => //=.
          ++ apply Int32_increment => //=.
        -- (* backward *)
          remember (Wasm_int.int_sub i32m (Wasm_int.int_add i32m s0 s2)
                      Wasm_int.Int32.one) as s0'.
          remember (Wasm_int.int_sub i32m (Wasm_int.int_add i32m s1 s2)
                      Wasm_int.Int32.one) as s1'.
          remember (Wasm_int.int_add i32m s2 Wasm_int.Int32.one) as s2'.
          exists s, f, [:: $VAN VAL_int32 s0'; $VAN VAL_int32 s1';
            AI_basic (BI_load T_i32 (Some (Tp_i8, SX_U)) 0%N 0%N);
            AI_basic (BI_store T_i32 (Some Tp_i8) 0%N 0%N);
            $VAN VAL_int32 s0; $VAN VAL_int32 s1; $VAN VAL_int32 s2';
            AI_basic BI_memory_copy], hs.
          apply r_memory_copy_backward with (mem := mem) => //=.
          move/negP in Emode. move/negP in Emode.
          rewrite -ltnNge in Emode. by rewrite Emode.
          ++ apply Int32_increment => //=.
          ++ apply Int32_add_decrement => //=.
          ++ apply Int32_add_decrement => //=.
    + exists s, f, [:: AI_trap], hs.
      apply r_memory_copy_bound with (mem := mem) => //=.
      left. move/negP in Ememss. move/negP in Ememss.
      rewrite -ltnNge in Ememss. by rewrite Ememss.
    + exists s, f, [:: AI_trap], hs.
      apply r_memory_copy_bound with (mem := mem) => //=.
      right. move/negP in Ememsd. move/negP in Ememsd.
      rewrite -ltnNge in Ememsd. by rewrite Ememsd.
    + exists s, f, [:: AI_trap], hs.
      apply r_memory_copy_bound with (mem := mem)=> //=.
      right. move/negP in Ememsd. move/negP in Ememsd.
      rewrite -ltnNge in Ememsd. by rewrite Ememsd.

  - (* Memory_init *)
    right. invert_typeof_vcs. simpl in *.
    destruct v as [[]| |], v0 as [[]| |], v1 as [[]| |] => //=.
    clear H1 H2 ETf HConstType.

    assert (exists mem, smem s f.(f_inst) = Some mem) as Hmem.
    {
      unfold smem.
      assert (size (tc_memory C0) > 0);
        first by destruct C0, tc_memory => //=.
      
      assert (size (inst_mems (f_inst f)) > 0);
        first by unfold inst_typing, typing.inst_typing in HIT;
        destruct C0, (f_inst f), tc_elem, tc_data,
                tc_local, tc_label, tc_return, tc_ref => //;
        remove_bools_options; rewrite all2E in H3;
        remove_bools_options; rewrite H3 => //=.

      destruct (inst_mems (f_inst f)) eqn:Einst => //=.
      assert (List.nth_error (inst_mems (f_inst f)) 0 = Some m);
        first by rewrite Einst.
      
      remember HIT as HIT'. clear HeqHIT'.
      eapply inst_index_get_contextval_mem in HIT'; eauto.
      destruct HIT' as [a Ha].

      eapply inst_typing_mem in HIT; eauto.
    }
    destruct Hmem as [mem Hmem].

    assert (exists data, sdata s f.(f_inst) x = Some data) as Hdata.
    {
      admit. 
      (* data here, not table *)

      (* remember HIT as HIT'. clear HeqHIT'.
      eapply inst_index_get_instval_tab in HIT'; eauto.
      destruct HIT' as [a Ha].

      unfold stab.
      unfold inst_typing, typing.inst_typing in HIT.
      destruct C0, (f_inst f), tc_elem, tc_data,
              tc_local, tc_label, tc_return, tc_ref => //.
      remove_bools_options.
      simpl in H. unfold tabi_agree in H4.
      eapply all2_projection in H4; eauto.
      simpl in *. unfold lookup_N.
      remove_bools_options. rewrite Ha; eauto. *)
    }
    destruct Hdata as [data Hdata].

    destruct (mem_length mem >= Wasm_int.N_of_uint i32m s0 + Wasm_int.N_of_uint i32m s2) eqn:Etabs;
    destruct (data_size data >= Wasm_int.nat_of_uint i32m s1 + Wasm_int.nat_of_uint i32m s2) eqn:Eelems.
    + destruct (s2 == Wasm_int.int_zero i32m) eqn:En; move/eqP in En.
      * exists s, f, [::], hs.
        apply r_memory_init_return with (mem := mem) (data := data) => //=.
      * destruct (lookup_N (datainst_data data) (Wasm_int.N_of_uint i32m s1)) eqn:Eeleml.
        -- remember (Wasm_int.int_add i32m s0 Wasm_int.Int32.one) as s0'.
          remember (Wasm_int.int_add i32m s1 Wasm_int.Int32.one) as s1'.
          remember (Wasm_int.int_sub i32m s2 Wasm_int.Int32.one) as s2'.
          exists s, f, [:: $VAN VAL_int32 s0;
              v_to_e (VAL_num (wasm_deserialise [:: b] T_i32));
              AI_basic (BI_store T_i32 (Some Tp_i8) 0%N 0%N);
              $VAN VAL_int32 s0'; $VAN VAL_int32 s1'; $VAN VAL_int32 s2';
              AI_basic (BI_memory_init x)], hs.
          apply r_memory_init_step with (mem := mem) (data := data) => //=.
          ++ apply Int32_decrement => //=.
          ++ apply Int32_increment => //=.
          ++ apply Int32_increment => //=.
        -- admit. (* fix using above, this is impossible *)
    + exists s, f, [:: AI_trap], hs.
      apply r_memory_init_bound with (mem := mem) (data := data) => //=.
      left. move/negP in Eelems. move/negP in Eelems.
      rewrite -ltnNge in Eelems. by rewrite Eelems.
    + exists s, f, [:: AI_trap], hs.
      apply r_memory_init_bound with (mem := mem) (data := data) => //=.
      right. move/negP in Etabs. move/negP in Etabs.
      rewrite -ltnNge in Etabs. by rewrite Etabs.
    + exists s, f, [:: AI_trap], hs.
      apply r_memory_init_bound with (mem := mem) (data := data) => //=.
      right. move/negP in Etabs. move/negP in Etabs.
      rewrite -ltnNge in Etabs. by rewrite Etabs.
  
  - (* Data_drop *)
    right. invert_typeof_vcs. simpl in *.
    clear H0 H1 ETf HConstType.
    (* same as using HIT:inst_typing to get [datainst] using
        "lookup_N (s_datas s)"@ "inst_datas (f_inst f)"@ x *)
    (* then matching with H:lookup (tc_data C0) x to get [s'] using
        "s_datas := set_nth [::] (s_datas s) (N.to_nat x) [::]" *)
    destruct (sdata_drop s f.(f_inst) x) eqn:Edata.
    + unfold sdata_drop in Edata.
      exists s0, f, [::], hs.
      apply r_data_drop => //=.
    + admit. (* fix using above, this is impossible *)

  - (* Composition *)
    subst.
    rewrite to_e_list_cat in HNBI_br.
    rewrite to_e_list_cat in HNRet.
    clear H.
    edestruct IHHType1; eauto.
    { by eapply nlfbr_right; eauto. }
    { by eapply nlfret_right; eauto. }
    + (* Const *)
      apply const_es_exists in H. destruct H as [cs HConst].
      apply b_e_elim in HConst. destruct HConst. subst.
      remember (to_b_list (v_to_e_list cs)) as bcs.
      rewrite -(e_b_elim Heqbcs H2) in HNRet.
      rewrite -(e_b_elim Heqbcs H2) in HNBI_br.

      eapply ety_a with (s := s) in HType1.
      rewrite -(e_b_elim Heqbcs H2) in HType1.
      apply const_list_typing in HType1; last apply v_to_e_is_const_list.
      destruct HType1 as [HType1f HType1].
      subst t2s.
      edestruct IHHType2; eauto.
      { eapply nlfbr_left; try apply v_to_e_is_const_list; eauto. }
      { eapply nlfret_left; try apply v_to_e_is_const_list; eauto. }
      { by rewrite -map_cat. }
      * left. rewrite to_e_list_cat. apply const_list_concat => //.
        rewrite -(e_b_elim Heqbcs H2). apply v_to_e_is_const_list.
      * destruct H as [es' HReduce]. right.
        rewrite to_e_list_cat.
        rewrite -(e_b_elim Heqbcs H2).
        (* last by apply const_list_is_basic; apply v_to_e_is_const_list. *)
        exists es'.
        rewrite catA.
        by rewrite v_to_e_cat.
    + (* reduce *)
      destruct H as [s' [vs' [es' [hs' HReduce]]]].
      right.
      rewrite to_e_list_cat.
      exists s', vs', (es' ++ to_e_list [::e]), hs'.
      rewrite catA.
      by apply reduce_composition_right.

  - (* Weakening *)
    apply cat_split in HConstType.
    destruct HConstType.
    rewrite -map_take in H1. rewrite -map_drop in H5.
    subst.
    edestruct IHHType; eauto.
    right.
    destruct H2 as [s' [f' [es' [hs' HReduce]]]].
    replace vcs with (take (size ts) vcs ++ drop (size ts) vcs); last by apply cat_take_drop.
    rewrite -v_to_e_cat. rewrite -catA.
    exists s', f', (v_to_e_list (take (size ts) vcs) ++ es'), hs'.
    apply reduce_composition_left => //.
    by apply v_to_e_is_const_list.
(* Qed. *) Admitted.

(*
Traceback:
  WTP: config_typing i s vs es ts <=
       s_typing s None i vs es ts && (store_typing s) <=
       e_typing s (C [local = map typeof vs, label = [::], return = None]) es (Tf [::] ts) && ...

  So we only need the part of e_typing with label and return being empty.

  However, it's insufficient to state the e_typing lemma as above, since non-empty label and
    return are required for the Local and AI_label cases respectively.

  Note that for BI_br i to be typeable, the length of label must be at least i+1 due to the
    requirement List.nth_error (tc_label C) i = Some ts. This means that there must be
    at least k+1 labels below the current BI_br i instruction. So say if the current instruction
    list satisfies lfilled n ..., then we have i<n.

  In particular, since in the be_typing case we have no labels (as label is not a basic
    instruction, we have i<0, i.e. we don't need to deal with BI_br there!

  Similarly, for Return to be typeable, tc_return C must be not None; but that is the case
    only if there's already a Local outside the Return instruction. So we don't have to deal
    with Return in be_typing either.
 *)

Definition br_reduce (es: seq administrative_instruction) :=
  exists n lh, @lfilled n lh [::AI_basic (BI_br (bin_of_nat n))] es.

Definition return_reduce (es: seq administrative_instruction) :=
  exists n lh, @lfilled n lh [::AI_basic BI_return] es.

(* pickable2_weaken no longer applicable
 *  since existential (lh: lholed x) depends on function input (x: nat)
 * Does this mean these aren't true since they have dependent types?
 *)

(** [br_reduce] is decidable. **)
Lemma br_reduce_decidable : forall es, decidable (br_reduce es).
Proof. admit.
  (* move=> es. apply: pickable_decidable. apply: pickable2_weaken.
  apply lfilled_pickable_rec_gen => // es' lh lh' n.
  by apply: lfilled_decidable_base. *)
(* Defined. *) Admitted.

(** [return_reduce] is decidable. **)
Lemma return_reduce_decidable : forall es, decidable (return_reduce es).
Proof. admit.
  (* move=> es. apply: pickable_decidable. apply: pickable2_weaken.
  apply lfilled_pickable_rec => // es'.
  by apply: lfilled_decidable_base. *)
(* Defined. *) Admitted.


Local Lemma cat_abcd_a_bc_d: forall {X:Type} (a b c d: seq X),
    a ++ b ++ c ++ d = a ++ (b ++ c) ++ d.
Proof.
  move => X a b c d.
  f_equal. by rewrite catA.
Qed.

Lemma br_reduce_label_length: forall n k lh es s C ts2,
    @lfilled n lh [::AI_basic (BI_br (bin_of_nat (n + k)))] es ->
    e_typing s C es (Tf [::] ts2) ->
    length (tc_label C) > k.
Proof.
  move => n k.
  generalize dependent k;
  induction n; dependent destruction lh => //;
  [| replace (nat_of_bin (bin_of_nat n.+1)) with (n.+1);
      last by symmetry; apply bin_of_natK ];
  move => es s C ts2 HLF HType;
  unfold lfilled in HLF; simpl in HLF; move/eqP in HLF; subst es;
  rewrite -cat1s in HType; invert_e_typing;
  destruct ts => //=; destruct t1s => //=; clear H1.
  - rewrite add0n in H5.
    apply et_to_bet in H5; auto_basic.
    simpl in H5. eapply Break_typing in H5; eauto.
    destruct H5 as [ts [ts2 [H7 [H8 H9]]]].
    unfold lookup_N in H8.
    assert (List.nth_error (tc_label C) (N.to_nat (bin_of_nat k)) <> None);
    first by rewrite H8.
    apply/ltP.
    rewrite nat_of_bin_is_N_to_nat in H8 => //=.
    replace (nat_of_bin (bin_of_nat k)) with (k) in H8;
      last by symmetry; rewrite bin_of_natK.
    apply List.nth_error_Some. by rewrite H8.
  - replace (N.pos (pos_of_nat (n + k)%Nrec (n + k)%Nrec))
      with (bin_of_nat (n.+1 + k)) in * => //.
    
    assert (Inf : k+1 < length (tc_label (upd_label C ([::ts1] ++ tc_label C))));
      first by eapply IHn with (lh := lh); eauto;
      rewrite addSnnS addn1; unfold lfilled.
    simpl in Inf. by lias.
Qed.

Lemma return_reduce_return_some: forall n lh es s C ts2,
    @lfilled n lh [::AI_basic BI_return] es ->
    e_typing s C es (Tf [::] ts2) ->
    tc_return C <> None.
Proof.
  move => n lh es s C ts2 HLF.
  generalize dependent ts2.
  generalize dependent C. generalize dependent s.
  dependent induction lh => //=; move => s C ts2 HType;
  unfold lfilled in HLF; simpl in HLF; move/eqP in HLF; subst es;
  rewrite -cat1s in HType; invert_e_typing;
  destruct ts => //=; destruct t1s => //=; clear H1.
  - apply et_to_bet in H5; auto_basic.
    simpl in H5.
    eapply Return_typing in H5; eauto.
    destruct H5 as [ts [ts' [H7 H8]]]. subst.
    by rewrite H8.
  - (* eapply IHlh; eauto. *)
    assert (R : tc_return (upd_label C ([::ts1] ++ tc_label C)) <> None);
      first by eapply IHlh; eauto; by unfold lfilled.
    by simpl in R.
Qed.

(* (N.to_nat (bin_of_nat n)) is intentional to
    emulate the use of labelidx (bin_of_nat n) as required by rs_br *)
Lemma br_reduce_extract_vs: forall n k lh es s C ts ts2,
    @lfilled n lh [::AI_basic (BI_br (bin_of_nat (n + k)))] es ->
    e_typing s C es (Tf [::] ts2) ->
    List.nth_error (tc_label C) k = Some ts ->
    exists vs lh', const_list vs /\
      @lfilled (nat_of_bin (bin_of_nat n)) lh' (vs ++ [::AI_basic (BI_br (bin_of_nat (n + k)))]) es /\
      length vs = length ts.
Proof.
  move => n k.
  generalize dependent k;
  induction n; dependent destruction lh => //;
  [| replace (nat_of_bin (bin_of_nat n.+1)) with (n.+1);
      last by symmetry; apply bin_of_natK ];
  move => es s C ts ts2 HLF HType HN;
  unfold lfilled in HLF; simpl in HLF; move/eqP in HLF; subst es;
  rewrite -cat1s in HType; invert_e_typing;
  destruct ts0 => //; destruct t1s => //; clear H1.
  (* dependent induction HLF; subst; move => s C ts2 ts HType HN. *)
  - rewrite add0n in H5.
    apply et_to_bet in H5; auto_basic.
    simpl in H5.
    eapply Break_typing in H5; eauto.
    destruct H5 as [ts3 [ts3' [H7 [H8 H9]]]]. subst.
    (* unfold plop2 in H8. move/eqP in H8. *)
    unfold lookup_N in H8.
    rewrite nat_of_bin_is_N_to_nat in H8 => //=.
    replace (nat_of_bin (bin_of_nat k)) with (k) in H8;
      last by symmetry; rewrite bin_of_natK.
    rewrite HN in H8. inversion H8. subst. clear H8.
    assert (const_list (v_to_e_list l)). {
      unfold const_list, v_to_e_list. apply List.forallb_forall.
      intros. apply List.in_map_iff in H. destruct H as [?[? ?]].
      rewrite -H. destruct x0, v => //=.
    }
    remember H as H'. clear HeqH'.
    apply const_es_exists in H.
    destruct H as [vs' H]. subst.
    apply const_list_typing in H3 => //=. simpl in H3.
    destruct H3 as [H3f H3].
    rewrite catA in H3. symmetry in H3.
    apply cat_split in H3. destruct H3.
    replace l with (take (size (ts1 ++ ts3')) l
                      ++ drop (size (ts1 ++ ts3')) l);
      last by apply cat_take_drop.
    exists (v_to_e_list (drop (size (ts1 ++ ts3')) l)),
            (LH_base (take (size (ts1 ++ ts3')) l) l0).
    repeat split.
    + by apply v_to_e_is_const_list.
    + (* apply/lfilledP. *)
      rewrite -v_to_e_cat. rewrite -catA.
      rewrite -(cat1s (AI_basic (BI_br (bin_of_nat (0 + k)))) l0).
      rewrite cat_abcd_a_bc_d. unfold lfilled. apply/eqP. simpl.
      f_equal.
    + rewrite H1. unfold v_to_e_list, vs_to_vts.
      repeat rewrite length_is_size. rewrite -map_drop.
      repeat rewrite size_map => //=.
  - replace (N.pos (pos_of_nat (n + k)%Nrec (n + k)%Nrec))
       with (bin_of_nat (n.+1 + k)) in * => //.
    edestruct IHn with (k := k.+1) (lh := lh); eauto;
      first by rewrite addnS addSn; unfold lfilled.
    replace (nat_of_bin (bin_of_nat n)) with n in H;
      last by symmetry; apply bin_of_natK.
    destruct H as [lh2 [HConst [HLF2 HLength]]].
    exists x, (LH_rec l (length ts2) l0 lh2 l1).
    repeat split => //. unfold lfilled in * => //.
    move/eqP in HLF2. rewrite -addSnnS in HLF2. simpl.
    replace (N.pos (pos_of_nat (n + k)%Nrec (n + k)%Nrec))
       with (bin_of_nat (n.+1 + k)) in * => //.
    by rewrite HLF2.
Qed.

Lemma return_reduce_extract_vs: forall n lh es s C ts ts2,
    @lfilled n lh [::AI_basic BI_return] es ->
    e_typing s C es (Tf [::] ts2) ->
    tc_return C = Some ts ->
    exists vs lh', const_list vs /\
      @lfilled (nat_of_bin (bin_of_nat n)) lh' (vs ++ [::AI_basic BI_return]) es /\
      length vs = length ts.
Proof.
  dependent induction lh => //;
  [| replace (nat_of_bin (bin_of_nat k.+1)) with (k.+1);
      last by symmetry; apply bin_of_natK ];
  move => es s C ts ts2 HLF HType HN;
  unfold lfilled in HLF; simpl in HLF; move/eqP in HLF; subst es;
  rewrite -cat1s in HType; invert_e_typing;
  destruct ts0 => //; destruct t1s => //; clear H1.
  - apply et_to_bet in H5; auto_basic.
    simpl in H5.
    eapply Return_typing in H5; eauto.
    destruct H5 as [ts2 [ts2' [H7 H8]]]. subst.
    rewrite HN in H8. inversion H8. subst.
    assert (const_list (v_to_e_list l)). {
      unfold const_list, v_to_e_list. apply List.forallb_forall.
      intros. apply List.in_map_iff in H. destruct H as [?[? ?]].
      rewrite -H. destruct x0, v => //=.
    }
    remember H as H'. clear HeqH'.
    apply const_es_exists in H.
    destruct H as [vs' H]. subst.
    apply const_list_typing in H3 => //=. simpl in H3.
    destruct H3 as [H3f H3].
    rewrite catA in H3. symmetry in H3.
    apply cat_split in H3. destruct H3.
    replace l with (take (size (ts1 ++ ts2')) l
                    ++ drop (size (ts1 ++ ts2')) l);
      last by apply cat_take_drop.
    exists (v_to_e_list (drop (size (ts1 ++ ts2')) l)),
          (LH_base (take (size (ts1 ++ ts2')) l) l0).
    repeat split.
    + by apply v_to_e_is_const_list.
    + rewrite -v_to_e_cat. rewrite -catA.
      rewrite -(cat1s (AI_basic (BI_return)) l0).
      rewrite cat_abcd_a_bc_d. unfold lfilled. apply/eqP. simpl.
      f_equal.
    + rewrite H1. unfold v_to_e_list, vs_to_vts.
      repeat rewrite length_is_size. rewrite -map_drop.
      repeat rewrite size_map => //=.
  - replace (nat_of_bin (bin_of_nat k)) with (k) in IHlh;
      last by symmetry; apply bin_of_natK.
    edestruct IHlh; eauto; first by unfold lfilled.
    destruct H as [lh2 [HConst [HLF2 HLength]]].
    exists x, (LH_rec l (length ts2) l0 lh2 l1).
    repeat split => //=. unfold lfilled in * => //.
    move/eqP in HLF2. simpl. by rewrite HLF2.
Qed.

Lemma le_add: forall n m,
    n <= m ->
    exists k, m = n+k.
Proof.
  move => n m. move: m n.
  elim => [|m].
  - move => n Hn. exists 0.
    case: n Hn => //=.
  - move => IHm.
    case => [|n] Hn.
    + by exists (m.+1).
    + move: (IHm n Hn) => [k Hk].
      exists k.
      by lias.
Qed.

(*
  These two guarantees that the extra conditions we put in progress_e are true -- the second
    being true only if the function doesn't return anything (so we are not in the middle of some
    Local functions).
*)
Lemma s_typing_lf_br: forall s rs f es ts,
    s_typing s rs f es ts ->
    (forall n lh k, @lfilled n lh [::AI_basic (BI_br (bin_of_nat k))] es -> k < n).
Proof.
  move => s rs f es ts HType n lh k HLF.
  inversion HType. inversion H. subst.
  destruct (k<n) eqn: H3 => //=.
  move/ltP in H3.
  assert (Inf : n <= k); first by lias.
  apply le_add in Inf.
  destruct Inf as [j Inf]. subst.
  clear H3.
  eapply br_reduce_label_length in H1; eauto.
  simpl in H1.
  assert (E : tc_label C1 = [::]); first by eapply inst_t_context_label_empty; eauto.
  by rewrite E in H1.
Qed.

Lemma s_typing_lf_return: forall s f es ts,
    s_typing s None f es ts ->
    (forall n, not_lf_return es n).
Proof.
  unfold not_lf_return.
  move => s f es ts HType n lh HContra.
  inversion HType; subst.
  by eapply return_reduce_return_some in H1; eauto.
Qed.

Axiom host_application_exists: forall hs s tf hf vcs,
    exists hs' res, host_application hs s tf hf vcs hs' res.

Lemma value_list_not_trap: forall vcs,
  v_to_e_list vcs = [:: AI_trap] -> False.
Proof.
  intros.
  induction vcs => //=.
  unfold v_to_e_list in H.
  rewrite map_cons -cat1s in H.
  fold (v_to_e_list vcs) in H.

  assert (forall X (xs xs' : seq X), xs = xs' -> size xs = size xs').
    intros; by rewrite H0.

  remember H as H'. clear HeqH'.
  apply H0 in H. simpl in H. replace (1) with (0 + 1) in H => //. rewrite -addn1 in H.
  move/eqP in H. rewrite eqn_add2r in H. move/eqP in H. apply size0nil in H.
  rewrite H in H'. simpl in H'.

  destruct a as [| |[]] => //=.
Qed.

Lemma t_progress_e: forall s C C' f vcs es tf ts1 ts2 lab ret hs,
    e_typing s C es tf ->
    tf = Tf ts1 ts2 ->
    C = (upd_label (upd_local_label_return C' (map typeof f.(f_locs)) (tc_label C') ret) lab) ->
    inst_typing s f.(f_inst) C' ->
    map typeof vcs = ts1 ->
    store_typing s ->
    (forall n lh k, @lfilled n lh [::AI_basic (BI_br (bin_of_nat k))] es -> k < n) ->
    (forall n, not_lf_return es n) ->
    terminal_form (v_to_e_list vcs ++ es) \/
    exists s' f' es' hs', reduce hs s f (v_to_e_list vcs ++ es) hs' s' f' es'.
Proof.
  (* e_typing *)
  move => s C C' f vcs es tf ts1 ts2 lab ret hs HType.
  move: f C' vcs ts1 ts2 lab ret hs.
  (* Initially I had the wrong order of lab and ret --
       The error message here is extremely misleading *)
  apply e_typing_ind' with (e := HType)
    (P := fun s C es tf (_ : e_typing s C es tf) => forall f C' vcs ts1 ts2 lab ret hs,
              tf = Tf ts1 ts2 ->
              C = (upd_label (upd_local_label_return C' (map typeof f.(f_locs)) (tc_label C') ret) lab) ->
              inst_typing s f.(f_inst) C' ->
              map typeof vcs = ts1 ->
              store_typing s ->
              (forall n lh k, @lfilled n lh [::AI_basic (BI_br (bin_of_nat k))] es -> k < n) ->
              (forall n, not_lf_return es n) ->
              terminal_form (v_to_e_list vcs ++ es) \/
              exists s' f' es' hs', reduce hs s f (v_to_e_list vcs ++ es) hs' s' f' es')
    (P0 := fun s rs f es ts (_ : s_typing s rs f es ts) => forall hs,
              store_typing s ->
              (forall n lh k, @lfilled n lh [::AI_basic (BI_br (bin_of_nat k))] es -> k < n) ->
              (forall n, not_lf_return es n) ->
              (const_list es /\ length es = length ts) \/
              es = [::AI_trap] \/
              exists s' f' es' hs', reduce hs s f es hs' s' f' es'); clear HType s C es tf.
  (* The previous variables s/C/es/tf still lingers here so we need to clear *)
  (* UPD (23 Sep 2020): with the new wrapper approach to deal with host, we can no longer
     clear everything like we did originally: this is because the clear tactic also 
     removes some section variables which make application of t_progress_be impossible
     (in this case, it's function_closure). See https://github.com/coq/coq/pull/883*)
  - (* AI_basic *)
    move => s C bes tf HType.
    move => f C' vcs ts1 ts2 lab ret hs HTF HContext HInst HConstType HST HBI_brDepth HNRet.
    subst.
    eapply t_progress_be in HType; try instantiate (1 := vs) in HType; try by eauto.
    destruct HType as [HType | [s' [vs' [es' [hs' HType]]]]].
    + left.
      unfold terminal_form; left.
      apply const_list_concat => //. by apply v_to_e_is_const_list.
    + right.
      repeat eexists. by apply HType.
    + unfold not_lf_br. move => k lh HContra.
      remember (N.to_nat k) as k'. assert (bin_of_nat k' = k);
        first by rewrite Heqk' nat_of_bin_is_N_to_nat => //;
        apply nat_of_binK.
      rewrite -H in HContra. apply HBI_brDepth in HContra => //=.

  - (* Composition *)
    move => s C es e t1s t2s t3s HType1 IHHType1 HType2 IHHType2.
    move => f C' vcs ts1 ts2 lab ret hs HTF HContext HInst HConstType HST HBI_brDepth HNRet.
    inversion HTF; subst.
    edestruct IHHType1; eauto.
    { move => n lh k HLF.
      eapply lf_composition in HLF.
      destruct HLF as [lh' HLF].
      instantiate (1 := [::e]) in HLF.
      eapply HBI_brDepth.
      by apply HLF. }
    { move => n.
      eapply nlfret_right. by apply HNRet. }
    + (* Terminal *)
      unfold terminal_form in H. destruct H.
      * (* Const *)
        apply const_list_split in H. destruct H as [HC1 HC2].
        (* apply et_to_bet in HType1 => //=. last by apply const_list_is_basic. *)
        apply const_es_exists in HC2.
        destruct HC2 as [esv HC2]. subst.
        assert (const_list (v_to_e_list esv)). {
          unfold const_list, v_to_e_list. apply List.forallb_forall.
          intros. apply List.in_map_iff in H. destruct H as [?[? ?]].
          rewrite -H. destruct x0, v => //=.
        }
        apply const_list_typing in HType1 => //=. subst.
        destruct HType1 as [HType1f HType1].
        subst t2s.
        edestruct IHHType2; eauto.
        { by apply map_cat. }
        { move => n lh k HLF.
          eapply lf_composition_left 
             with (cs := v_to_e_list esv) in HLF => //.
          destruct HLF as [lh' HLF].
          eapply HBI_brDepth; eauto. }
        { move => n.
          eapply nlfret_left.
          (* first by apply v_to_e_is_const_list. [esv] *)
          instantiate (1 := v_to_e_list esv).
          apply v_to_e_is_const_list.
          by apply HNRet. }
        -- (* Terminal *)
          unfold terminal_form in H. destruct H.
          ++ left. rewrite -v_to_e_cat in H0.
             by rewrite catA.
        -- (* reduce *)
          rewrite -v_to_e_cat in H0.
          rewrite -catA in H0.
          right.
          by eapply H0.
      * (* AI_trap *)
        induction es => //=.
        -- rewrite cats0 in H.
          apply value_list_not_trap in H. destruct H.
        simpl in H. inversion H. subst.
        right.
        exists s, f, [::AI_trap], hs.
        apply r_simple.
        eapply rs_trap with (lh := (LH_base [::] [::e])) => //;
          last by unfold lfilled; simpl; rewrite -cat1s -H1;
            apply/eqP; rewrite -catA => //=.
        rewrite (catA (v_to_e_list vcs) (a :: es) [:: e]) H1.
        lias.
    + (* reduce *)
      destruct H as [s' [f' [es' [hs' HReduce]]]].
      right.
      exists s', f', (es' ++ [::e]), hs'.
      eapply r_label; eauto; try apply/lfilledP;
      try instantiate (1 := (LH_base [::] [::e]));
      unfold lfilled; simpl => //=. by rewrite catA.
  - (* Weakening *)
    (* This is interestingly easy. Think more carefully: the only part that is
       relevant in the reduction is ts1, but ts1 is only required for typing the
       const list. So we just separate the new const list into 2 parts and add
       the first part to the result correspondingly! *)
    move => s C es ts t1s t2s HType IHHType.
    move => f C' vcs ts1 ts2 lab ret hs' HTF HContext HInst HConstType HST HBI_brDepth HNRet.
    inversion HTF; subst.
    symmetry in H0. apply cat_split in H0. destruct H0 as [HCT1 HCT2].
    rewrite - map_take in HCT1.
    rewrite - map_drop in HCT2.
    assert (Evcs : vcs = take (size ts) vcs ++ drop (size ts) vcs).
    { symmetry. by apply cat_take_drop. }
    rewrite Evcs. rewrite - v_to_e_cat.
    edestruct IHHType; eauto.
    + (* Terminal *)
      unfold terminal_form in H.
      destruct H => //=.
      * (* Const *)
        left. unfold terminal_form. left.
        rewrite -catA. apply const_list_concat => //.
        by apply v_to_e_is_const_list.
      * (* AI_trap *)
        apply v_e_trap in H; last by apply v_to_e_is_const_list.
        destruct H. subst.
        rewrite H.
        destruct (drop (size ts) vcs) eqn:HDrop => //=.
        clear H. rewrite cats0 in Evcs. rewrite -Evcs.
        rewrite cats0.
        destruct vcs => //.
        -- left. by apply terminal_trap.
        -- right.
           exists s, f, [::AI_trap], hs'.
           apply r_simple.
           apply reduce_trap_left => //.
           by apply v_to_e_is_const_list.
    + (* reduce *)
      destruct H as [s' [f' [es' [hs'' HReduce]]]].
      right.
      exists s', f', (v_to_e_list (take (size ts) vcs) ++ es'), hs''.
      rewrite -catA.
      apply reduce_composition_left => //; first by apply v_to_e_is_const_list.
      by eapply HReduce.
      
  - (* Trap *)
    destruct vcs => //; first by left; apply terminal_trap.
    right.
    exists s, f, [::AI_trap], hs.
    apply r_simple.
    apply reduce_trap_left => //.
    by apply v_to_e_is_const_list.

  - (* Ref_extern*)
    move => s C a f C' vcs ts1 t2s lab ret hs
            HTF HContext HInst HConstType HST HBI_brDepth HTerminal.
    inversion HTF; subst. destruct vcs => //=.
    left. unfold terminal_form.
    left. unfold const_list, is_const.
    apply List.forallb_forall. intros x H.
    inversion H => //. rewrite -H1; eauto.

  - (* Ref*)
    move => s C a tf HFunc f C' vcs ts1 t2s lab ret hs
            HTF HContext HInst HConstType HST HBI_brDepth HTerminal.
    inversion HTF; subst. destruct vcs => //=.
    left. unfold terminal_form.
    left. unfold const_list, is_const.
    apply List.forallb_forall. intros x H.
    inversion H => //. rewrite -H1; eauto.

  - (* Invoke *)
    move => s a C cl tf HNth HType.
    move => f C' vcs ts1 ts2 lab ret hs HTF HContext HInst HConstType HST HBI_brDepth HNRet.
    inversion HType; subst.
    inversion H5; subst; clear H5.
    + (* Native *)
      right.
      exists s, f,
      [::AI_local (length ts2) (Build_frame (vcs ++ n_zeros ts) i)
      [::AI_label (length ts2) [::] (to_e_list es)]], hs.
      eapply r_invoke_native; eauto.
      repeat rewrite length_is_size. by rewrite size_map.
    + (* Host *)
      right.
      (* There are two possible reduction paths dependning on whether the host
          call was successful. However for the proof here we just have to show that
          on exists -- so just use the easier failure case. *)
      (* UPD: with the new host and the related reductions, this shortcut no longer
          works. We will now need to consider the result of host execution and 
          specify the reduction resultion result in either case. *)
      assert (HApply: exists hs' res,
        host_application hs s (Tf (map typeof vcs) ts2) h vcs hs' res).
      apply host_application_exists.
      destruct HApply as [hs' [res HApply]].
      destruct res as [opres |].
      destruct opres as [p r].
      * (* Some *)
        repeat eexists.
        eapply r_invoke_host_success; eauto.
        repeat rewrite length_is_size. by apply size_map.
      * (* None *)
        repeat eexists.
        eapply r_invoke_host_diverge; eauto.
        repeat rewrite length_is_size. by apply size_map.

  - (* Label *)
    move => s C e0s es ts t2s n HType1 IHHType1 HType2 IHHType2 HLength.
    move => f C' vcs ts1 ts2 lab ret hs HTF HContext HInst HConstType HST HBI_brDepth HNRet.
    inversion HTF; subst.
    symmetry in H0. invert_typeof_vcs.
    rewrite upd_label_overwrite in HType2. simpl in HType2.
    destruct (br_reduce_decidable es) as [HEMT | HEMF].
    { unfold br_reduce in HEMT.
      destruct HEMT as [n [lh HLF]].
      right.
      assert (LF : @lfilled n lh [::AI_basic (BI_br ((bin_of_nat (n+0))))] es);
      first by rewrite addn0.
      eapply br_reduce_extract_vs with (ts := ts) in LF => //; eauto.
      destruct LF as [cs [lh' [HConst [HLF2 HLength]]]]. rewrite addn0 in HLF2.
      repeat eexists. apply r_simple. eapply rs_br with (lh := lh'); eauto.
    }
    edestruct IHHType2; eauto.
    { rewrite upd_label_overwrite. simpl. eauto. }
    { unfold br_reduce in HEMF.
      move => n lh k HLF.
      assert (Inf : k < n.+1). (* FIXME: Proof items to be added here. *)
      { eapply HBI_brDepth.
      assert (LF : @lfilled (n.+1) (LH_rec [::] (length ts) e0s lh [::])
              [::AI_basic (BI_br (bin_of_nat k))]
              ([::] ++ [::AI_label (length ts) e0s es] ++ [::])).
        unfold lfilled. simpl. apply/eqP. f_equal. f_equal.
        unfold lfilled in HLF. apply/eqP => //=.
      rewrite cats0 in LF. simpl in LF.
      by apply LF. }
      rewrite ltnS in Inf.
      rewrite leq_eqVlt in Inf.
      remove_bools_options => //.
      subst.
      exfalso.
      apply HEMF. repeat eexists. by apply HLF.
    }
    { unfold not_lf_return.
      move => n lh HContra.
      unfold not_lf_return in HNRet.
      eapply HNRet.
      assert (LF : @lfilled (n.+1) (LH_rec [::] (length ts) e0s lh [::])
              [::AI_basic BI_return]
              ([::] ++ [::AI_label (length ts) e0s es] ++ [::])).
        unfold lfilled. simpl. apply/eqP. f_equal. f_equal.
        unfold lfilled in HContra. apply/eqP => //=.
      by apply LF.
    }
    + (* Terminal *)
      apply terminal_form_v_e in H.
      unfold terminal_form in H. destruct H.
      * (* Const *)
        right.
        exists s, f, es, hs.
        apply r_simple.
        by apply rs_label_const.
      * (* AI_trap *)
        right. subst.
        exists s, f, [::AI_trap], hs.
        apply r_simple.
        by apply rs_label_trap.
        by apply v_to_e_is_const_list.
    + (* reduce *)
      destruct H as [s' [f' [es' [hs' HReduce]]]].
      right.
      simpl in HReduce.
      exists s', f', [::AI_label (length ts) e0s es'], hs'.
      by eapply r_label; eauto; apply label_lfilled1.

  - (* Local *)
    move => s C n f0 es ts HType IHHType HLength.
    move => f C' vcs ts1 ts2 lab ret hs HTF HContext HInst HConstType HST HBI_brDepth HNRet.
    inversion HTF; subst; clear HTF.
    symmetry in H0.
    invert_typeof_vcs.
    right.
    destruct (return_reduce_decidable es) as [HEMT | HEMF].
    { inversion HType; subst.
      unfold return_reduce in HEMT.
      destruct HEMT as [n [lh HLF]].
      (* HEMT is almost what we need to prove the rs_return reduction, but we also need to prove
           that there are some consts of suitable length before the [::AI_basic Return] as well.
         Done as a separate lemma. *)
      eapply return_reduce_extract_vs in HLF; eauto; last by [].
      destruct HLF as [cs [lh' [HConst [HLF2 HLength]]]].
      repeat eexists. apply r_simple. eapply rs_return; eauto.
    }
    edestruct IHHType as [ | [ | ]]; eauto.
    {
      move => n lh k HLF.
      by eapply s_typing_lf_br in HLF; eauto.
    }
    { unfold return_reduce in HEMF. unfold not_lf_return.
      move => n lh HContra.
      apply HEMF. by eauto.
    }
    + (* Const *)
      destruct H.
      exists s, f, es, hs.
      apply r_simple.
      by apply rs_local_const.
    + (* AI_trap *)
      subst.
      exists s, f, [::AI_trap], hs.
      apply r_simple.
      by apply rs_local_trap.
    + (* reduce *)
      destruct H as [s' [f0' [es' [hs' HReduce]]]].
      exists s', f, [::AI_local (length ts2) f0' es'], hs'.
      by apply r_local; apply HReduce.

  - (* s_typing *)
    move => s f es rs ts C C0 HFT HContext HType IHHType HRetType hs HST HBI_brDepth HNRet.
    inversion HFT.
    subst.
    edestruct IHHType; eauto.
    { (* Context *)
      assert (E : tc_local C1 = [::]).
      { by eapply inst_t_context_local_empty; eauto. }
      rewrite E. simpl.
      (* HRetType: rs = Some ts \/ rs = None; shouldn't be optional? *)
      (* instantiate (1 := (tc_label C1)). instantiate (1 := rs).
      unfold upd_local_label_return, upd_local, upd_label, upd_return.
      simpl. f_equal. unfold upd_local_label_return. f_equal. *)
      by fold_upd_context. }
    { by instantiate (1 := [::]). }
    + unfold terminal_form in H0. destruct H0.
      * (* Const *)
        left.
        simpl in H0.
        split => //.
        apply const_es_exists in H0. destruct H0.
        rewrite H0 in HType.
        apply const_list_typing in HType;
          last by apply v_to_e_is_const_list.
        destruct HType as [HTypef HType].
        simpl in HType.
        rewrite HType H0 => //=. unfold v_to_e_list, vs_to_vts.
        repeat rewrite length_is_size. by repeat rewrite size_map.
      * (* AI_trap *)
        right. by left.
    + (* reduce *)
      simpl in H0. right. right. by eauto.
Qed.

Theorem t_progress: forall s f es ts hs,
    config_typing s f es ts ->
    terminal_form es \/
    exists s' f' es' hs', reduce hs s f es hs' s' f' es'.
Proof.
  move => s f es ts hs HType.
  inversion HType. inversion H0. inversion H5. subst.
  eapply t_progress_e with (vcs := [::]) (ret := None) (lab := [::]) in H7; eauto.
  - assert (E : tc_local C1 = [::]).
    { by eapply inst_t_context_local_empty; eauto. }
    rewrite E. simpl.
    fold_upd_context.
    assert (E' : tc_label (upd_local_label_return C1 (map typeof f.(f_locs)) (tc_label C1) None) = [::]).
    { simpl. by eapply inst_t_context_label_empty; eauto. }
    rewrite -E'.
    by destruct C1.
  - by eapply s_typing_lf_br; eauto.
  - by eapply s_typing_lf_return; eauto.
Qed.

End Host.
