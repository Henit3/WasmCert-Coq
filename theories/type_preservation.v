(** Proof of preservation **)
(* (C) Rao Xiaojia, M. Bodin - see LICENSE.txt *)

From Wasm Require Export common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From Coq Require Import Program.Equality NArith ZArith_base.
From Wasm Require Export operations datatypes_properties typing opsem properties.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Host.

Variable host_function : eqType.

Let store_record := store_record host_function.
Let function_closure := function_closure host_function.
Let e_typing : store_record -> t_context -> seq administrative_instruction -> function_type -> Prop :=
  @e_typing _.
Let inst_typing : store_record -> instance -> t_context -> bool := @inst_typing _.

Let host := host host_function.

Variable host_instance : host.

Let host_state := host_state host_instance.

Let reduce : host_state -> store_record -> frame -> seq administrative_instruction ->
             host_state -> store_record -> frame -> seq administrative_instruction -> Prop
  := @reduce _ _.

Let s_globals : store_record -> seq globalinst := @s_globals _.
Let s_mems : store_record -> seq meminst := @s_mems _.
Let cl_type : function_closure -> function_type := @cl_type _.
Let store_extension: store_record -> store_record -> Prop := @store_extension _.

Definition t_be_value bes : Prop :=
  const_list (to_e_list bes).

Ltac b_to_a_revert :=
  repeat lazymatch goal with
         | H:  to_e_list ?bes = _ |- _ =>
           apply b_e_elim in H; destruct H
         end.

Lemma b_e_elim: forall bes es,
    to_e_list bes = es ->
    bes = to_b_list es /\ es_is_basic es.
Proof.
  by apply properties.b_e_elim.
Qed.

Lemma upd_label_overwrite: forall C l1 l2,
    upd_label (upd_label C l1) l2 = upd_label C l2.
Proof.
  by [].
Qed.

Lemma N_div_le_mono': forall a b c,
  (c <> 0)%N ->
  (a / c <= b / c)%N ->
  (a <= b)%N.
Proof.
Admitted.

Lemma shift_scope_le_N: forall (a b : N),
  (a <= b)%N ->
  (a)%N <= b.
Proof.
Admitted.

(*
  These proofs are largely similar.
  A sensible thing to do is to make tactics for all of them.
  However, some of the proofs depend on the previous ones...
*)

(*
Lemma BI_const_typing: forall C econst t1s t2s,
  be_typing C [::BI_const econst] (Tf t1s t2s) ->
  t2s = t1s ++ [::typeof econst].
Proof.
  move => C econst t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.
*)

(*
  Perhaps have some tactic to solve these (same form)

  Ltac BI_const_typing_solve :=
    move => C econst t1s t2s HType;
    gen_ind_subst HType => //;
    [ apply extract_list1 in H1; inversion H1; subst;
      apply empty_typing in HType1; subst;
      by eapply IHHType2 |];
      [ rewrite catA; f_equal ];
      [ intros; by subst | by eapply IHHType ].
*)

Definition BI_const_num_typing: forall C econst t1s t2s,
  be_typing C [::BI_const_num econst] (Tf t1s t2s) ->
  t2s = t1s ++ [::T_num (typeof_num econst)].
Proof.
move => C econst t1s t2s HType.
gen_ind_subst HType => //.
- apply extract_list1 in H1; inversion H1; subst.
apply empty_typing in HType1; subst.
by eapply IHHType2.
- rewrite - catA. f_equal.
+ intros. by subst.
+ by eapply IHHType.
Qed.
Definition AI_const_num_typing: forall s C v t1s t2s,
  e_typing s C [::$VAN v] (Tf t1s t2s) ->
  t2s = t1s ++ [::T_num (typeof_num v)].
Proof.
  move => s C v t1s t2s HType.
  gen_ind_subst HType => //.
  - destruct bes => //=. unfold to_e_list in H3.
    rewrite -cat1s map_cat in H3. inversion H3.
    destruct bes => //=. simpl in *. subst.
    by apply BI_const_num_typing in H.
  - apply extract_list1 in H2; inversion H2; subst.
    apply e_empty_typing in HType1; subst.
    by eapply IHHType2.
  - rewrite - catA. f_equal. eapply IHHType => //=.
Qed.

Definition BI_const_vec_typing: forall C econst t1s t2s,
  be_typing C [::BI_const_vec econst] (Tf t1s t2s) ->
  t2s = t1s ++ [::T_vec (typeof_vec econst)].
Proof.
  move => C econst t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.
Definition AI_const_vec_typing: forall s C v t1s t2s,
  e_typing s C [::AI_basic (BI_const_vec v)] (Tf t1s t2s) ->
  t2s = t1s ++ [::T_vec (typeof_vec v)].
Proof.
  move => s C v t1s t2s HType.
  gen_ind_subst HType => //.
  - destruct bes => //=. unfold to_e_list in H3.
    rewrite -cat1s map_cat in H3. inversion H3.
    destruct bes => //=. simpl in *. subst.
    by apply BI_const_vec_typing in H.
  - apply extract_list1 in H2; inversion H2; subst.
    apply e_empty_typing in HType1; subst.
    by eapply IHHType2.
  - rewrite - catA. f_equal. eapply IHHType => //=.
Qed.

(* function ref constant? there is no [::BI_const_ref _] available *)
Definition BI_ref_null_typing: forall C econst t1s t2s,
  be_typing C [::BI_ref_null econst] (Tf t1s t2s) ->
  t2s = t1s ++ [::T_ref (typeof_ref (VAL_ref_null econst))].
Proof.
  move => C econst t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.
Definition AI_ref_null_typing: forall s C v t1s t2s,
  e_typing s C [::AI_basic (BI_ref_null v)] (Tf t1s t2s) ->
  t2s = t1s ++ [::T_ref (typeof_ref (VAL_ref_null v))].
Proof.
  move => s C v t1s t2s HType.
  gen_ind_subst HType => //.
  - destruct bes => //=. unfold to_e_list in H3.
    rewrite -cat1s map_cat in H3. inversion H3.
    destruct bes => //=. simpl in *. subst.
    by apply BI_ref_null_typing in H.
  - apply extract_list1 in H2; inversion H2; subst.
    apply e_empty_typing in HType1; subst.
    by eapply IHHType2.
  - rewrite - catA. f_equal. eapply IHHType => //=.
Qed.

Definition BI_ref_func_typing: forall C x t1s t2s,
  be_typing C [::BI_ref_func x] (Tf t1s t2s) ->
  exists t, lookup_N (tc_func C) x = Some t /\
            List.In x (tc_ref C) /\
            t2s = t1s ++ [::T_ref (typeof_ref (VAL_ref_func x))].
Proof.
  move => C x t1s t2s HType.
  gen_ind_subst HType => //.
  - exists t => //=. 
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists x0.
    repeat rewrite -catA.
    by repeat split => //=.
Qed.
(* 
Definition BI_ref_func_typing': forall C x t1s t2s,
  be_typing C [::BI_ref_func x] (Tf t1s t2s) ->
  (exists t, lookup_N (tc_func C) x = Some t) ->
  List.In x (tc_ref C) ->
  t2s = t1s ++ [::T_ref (typeof_ref (VAL_ref_func x))].
Proof.
  move => C x t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list1 in H1; inversion H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - rewrite - catA. f_equal.
    + intros _ _ H. by rewrite H.
    + eapply IHHType => //=.
Qed.
*)

Definition AI_ref_func_typing: forall s C v t1s t2s,
  e_typing s C [::AI_ref v] (Tf t1s t2s) ->
  exists tf, funci_agree s.(s_funcs) v tf /\
              t2s = t1s ++ [::T_ref T_funcref].
Proof.
  move => s C v t1s t2s HType.
  gen_ind_subst HType => //=.
  - destruct bes => //=.
  - apply extract_list1 in H2; inversion H2; subst.
    apply e_empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 H2]. subst.
    exists x.
    repeat rewrite -catA.
    by repeat split => //=.
  - exists tf. split => //=.
Qed.

Definition AI_ref_extern_typing: forall s C v t1s t2s,
  e_typing s C [::AI_ref_extern v] (Tf t1s t2s) ->
  t2s = t1s ++ [::T_ref T_externref].
Proof.
  move => s C v t1s t2s HType.
  gen_ind_subst HType => //=.
  - destruct bes => //=.
  - apply extract_list1 in H2; inversion H2; subst.
    apply e_empty_typing in HType1; subst.
    by eapply IHHType2.
  - rewrite - catA. f_equal. eapply IHHType => //=.
Qed.

Definition BI_const2_nn_typing: forall C econst1 econst2 t1s t2s,
  be_typing C [::BI_const_num econst1; BI_const_num econst2] (Tf t1s t2s) ->
  t2s = t1s ++ [::T_num (typeof_num econst1); T_num (typeof_num econst2)].
Proof.
  move => C econst1 econst2 t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list2 in H1; inversion H1; subst.
    apply BI_const_num_typing in HType1; subst.
    apply BI_const_num_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.
Definition BI_const2_vv_typing: forall C econst1 econst2 t1s t2s,
  be_typing C [::BI_const_vec econst1; BI_const_vec econst2] (Tf t1s t2s) ->
  t2s = t1s ++ [::T_vec (typeof_vec econst1); T_vec (typeof_vec econst2)].
Proof.
  move => C econst1 econst2 t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list2 in H1; inversion H1; subst.
    apply BI_const_vec_typing in HType1; subst.
    apply BI_const_vec_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.
Definition BI_const2_rr_typing: forall C econst1 econst2 t1s t2s,
  be_typing C [::BI_ref_null econst1; BI_ref_null econst2] (Tf t1s t2s) ->
  t2s = t1s ++ [::T_ref econst1; T_ref econst2].
Proof.
  move => C econst1 econst2 t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list2 in H1; inversion H1; subst.
    apply BI_ref_null_typing in HType1; subst.
    apply BI_ref_null_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.

Definition BI_const3_nnn_typing: forall C econst1 econst2 econst3 t1s t2s,
  be_typing C [::BI_const_num econst1; BI_const_num econst2; BI_const_num econst3] (Tf t1s t2s) ->
  t2s = t1s ++ [::T_num (typeof_num econst1); T_num (typeof_num econst2); T_num (typeof_num econst3)].
Proof.
  move => C econst1 econst2 econst3 t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list3 in H1; inversion H1; subst.
    apply BI_const2_nn_typing in HType1; subst.
    apply BI_const_num_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.
Definition BI_const3_vvn_typing: forall C econst1 econst2 econst3 t1s t2s,
  be_typing C [::BI_const_vec econst1; BI_const_vec econst2; BI_const_num econst3] (Tf t1s t2s) ->
  t2s = t1s ++ [::T_vec (typeof_vec econst1); T_vec (typeof_vec econst2); T_num (typeof_num econst3)].
Proof.
  move => C econst1 econst2 econst3 t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list3 in H1; inversion H1; subst.
    apply BI_const2_vv_typing in HType1; subst.
    apply BI_const_num_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.
(*
Definition BI_const3_vvv_typing: forall C econst1 econst2 econst3 t1s t2s,
  be_typing C [::BI_const_vec econst1; BI_const_vec econst2; BI_const_vec econst3] (Tf t1s t2s) ->
  t2s = t1s ++ [::T_vec (typeof_vec econst1); T_vec (typeof_vec econst2); T_vec (typeof_vec econst3)].
Proof.
  move => C econst1 econst2 econst3 t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list3 in H1; inversion H1; subst.
    apply BI_const2_vv_typing in HType1; subst.
    apply BI_const_vec_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.
*)
Definition BI_const3_rrn_typing: forall C econst1 econst2 econst3 t1s t2s,
  be_typing C [::BI_ref_null econst1; BI_ref_null econst2; BI_const_num econst3] (Tf t1s t2s) ->
  t2s = t1s ++ [::T_ref econst1; T_ref econst2; T_num (typeof_num econst3)].
Proof.
  move => C econst1 econst2 econst3 t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list3 in H1; inversion H1; subst.
    apply BI_const2_rr_typing in HType1; subst.
    apply BI_const_num_typing in HType2; subst.
    by rewrite -catA.
  - rewrite - catA. f_equal.
    + intros. by subst.
    + by eapply IHHType.
Qed.

Definition func_type_exists v s f :=
  exists tf, v = VAL_ref (VAL_ref_func f) ->
    @funci_agree host_function (s_funcs s) f tf.

Lemma const_typing: forall s C v t1s t2s,
  is_const (v_to_e v) ->
  e_typing s C [:: v_to_e v] (Tf t1s t2s) ->
  (forall f, (func_type_exists v s f)) /\
  t2s = t1s ++ [:: typeof v].
Proof.
  move => s C v.
  induction v as [| |[]] => //=; move => t1s t2s H HType;
  (* tf := (Tf [::] [::]) used to stop shelving tf specification *)
  split; try by (intro f; exists (Tf [::] [::]); intro Hf => //=).
  - by apply AI_const_num_typing in HType.
  - by apply AI_const_vec_typing in HType.
  - by apply AI_ref_null_typing in HType.
  - apply AI_ref_func_typing in HType.
    destruct HType as [tf [Hfunc _]].
    intros; exists tf; intro Hf.
    inversion Hf. subst => //=.
  - apply AI_ref_func_typing in HType.
    destruct HType as [tf [_ Hts]] => //=.
  - by apply AI_ref_extern_typing in HType.
Qed.

Lemma const_list_typing: forall s C vs t1s t2s,
  const_list (v_to_e_list vs) ->
  e_typing s C (v_to_e_list vs) (Tf t1s t2s) ->
  (forall v, v \in vs ->
    (forall f, (func_type_exists v s f))) /\
  t2s = t1s ++ (vs_to_vts vs).
Proof.
  move => s C vs.
  induction vs => //=; move => t1s t2s H HType.
  - apply e_empty_typing in HType. subst. by rewrite cats0.
  - move/andP in H. destruct H.
    rewrite -cat1s in HType.
    rewrite -cat1s.
    apply e_composition_typing in HType.
    destruct HType as [ts [ts1' [ts2' [ts3 [H1 [H2 [H3 H4]]]]]]].
    subst. apply IHvs in H4; eauto. subst. rewrite -catA. f_equal.
    rewrite catA. f_equal.
    apply const_typing in H3 => //=.
    destruct H3 as [H3 H3'] => //=.
    destruct H4 as [H4 H4']. subst.
    split => //=; last by repeat rewrite -catA.
    intros v Hv.
    rewrite in_cons in Hv. move/orP in Hv.
    destruct Hv; last by apply H4 => //=.
    move/eqP in H1. inversion H1. subst => //=.
Qed.

Lemma const_ref_typing': forall s C v,
  (is_numeric_type (typeof v) -> False) ->
  is_const (v_to_e v) ->
  (forall f,
    exists tf, v = VAL_ref (VAL_ref_func f) ->
    funci_agree (s_funcs s) f tf) ->
  e_typing s C [:: v_to_e v] (Tf [::] [:: typeof v]).
Proof.
  move => s C v HNum HConst HFunc.
  destruct v as [| |[]] => //=.
  - apply ety_a'; first by
      unfold es_is_basic, e_is_basic;
      apply List.Forall_cons; eauto.
    apply bet_ref_null.
  - destruct (HFunc f).
    eapply ety_ref; eauto.
  - apply ety_ref_extern.
Qed.

Lemma const_typing': forall s C v,
  is_const (v_to_e v) ->
  (forall f, (func_type_exists v s f)) ->
  e_typing s C [:: v_to_e v] (Tf [::] [:: typeof v]).
Proof.
  move => s C v HConst HFunc.
  destruct v as [| |[]] => //;
  try (
    simpl in *; apply ety_a'; try (
      unfold es_is_basic, e_is_basic;
      apply List.Forall_cons; eauto
    );
    simpl; constructor
  ); eapply const_ref_typing' => //=.
Qed.

Lemma const_list_typing': forall s C vs,
  const_list (v_to_e_list vs) ->
  (forall v, v \in vs ->
    (forall f, (func_type_exists v s f))) ->
  e_typing s C (v_to_e_list vs) (Tf [::] (vs_to_vts vs)).
Proof.
  move => s C vs.
  induction vs => //=; move => HConst HFunc.
  - apply ety_a' => //. apply bet_empty.
  - move/andP in HConst. destruct HConst.
    rewrite -cat1s -(cat1s (typeof a)).
    eapply et_composition' with (t2s := [:: typeof a]).
    + apply const_typing'; first by apply v_to_e_is_const.
      apply HFunc. apply mem_head.
    + apply et_weakening_empty_1. apply IHvs => //=.
      intros v Hv. apply HFunc. rewrite in_cons.
      apply/orP. by right.
Qed.


Lemma Unop_typing: forall C t op t1s t2s,
    be_typing C [::BI_unop t op] (Tf t1s t2s) ->
    t1s = t2s /\ exists ts, t1s = ts ++ [::T_num t].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - split => //=. by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    split => //=.
    destruct H0 as [ts' H0].
    exists (ts ++ ts').
    rewrite - catA.
    by rewrite H0.
Qed.

Lemma Binop_typing: forall C t op t1s t2s,
    be_typing C [::BI_binop t op] (Tf t1s t2s) ->
    t1s = t2s ++ [::T_num t] /\ exists ts, t2s = ts ++ [::T_num t].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - split => //=. by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    split => //=.
    + destruct H0 as [ts' H0].
      by rewrite - catA.
    + destruct H0 as [ts' H0].
      exists (ts ++ ts').
      subst.
      by rewrite - catA.
Qed.

Lemma Testop_typing: forall C t op t1s t2s,
    be_typing C [::BI_testop t op] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::T_num t] /\ t2s = ts ++ [::T_num T_i32].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

Lemma Relop_typing: forall C t op t1s t2s,
    be_typing C [::BI_relop t op] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::T_num t; T_num t] /\ t2s = ts ++ [::T_num T_i32].
Proof.
  move => C t op t1s t2s HType.
  gen_ind_subst HType.
  - by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

Lemma Cvtop_typing: forall C t1 t2 op sx t1s t2s,
    be_typing C [::BI_cvtop t2 op t1 sx] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::T_num t1] /\ t2s = ts ++ [::T_num t2].
Proof.
  move => C t1 t2 op sx t1s t2s HType.
  gen_ind_subst HType.
  - by exists [::].
  - by exists [::].
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    destruct H as [ts' H]. subst.
    exists (ts ++ x).
    by repeat rewrite - catA.
Qed.

Lemma Ref_is_null_typing: forall C t1s t2s,
    be_typing C [::BI_ref_is_null] (Tf t1s t2s) ->
    exists ts t, t1s = ts ++ [::T_ref t] /\ t2s = ts ++ [::T_num T_i32].
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType;
  try (exists [::], T_funcref; simpl; split; discriminate).
  - exists [::], t. simpl. split => //=.
  - apply extract_list1 in Econs; destruct Econs; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    destruct H as [t' [H1 H2]]. subst.
    exists (ts ++ x), t'.
    repeat rewrite - catA. split => //=.
Qed.

Lemma Nop_typing: forall C t1s t2s,
    be_typing C [::BI_nop] (Tf t1s t2s) ->
    t1s = t2s.
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //.
  - apply extract_list1 in Econs; destruct Econs; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - f_equal. by eapply IHHType.
Qed.

Lemma Drop_typing: forall C t1s t2s,
    be_typing C [::BI_drop] (Tf t1s t2s) ->
    exists t, t1s = t2s ++ [::t].
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //=.
  - by eauto.
  - apply extract_list1 in Econs; destruct Econs; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    exists x. repeat rewrite -catA. by f_equal.
Qed.

(* Lemma Select_typing_Some: forall C t1s t2s t,
    be_typing C [::BI_select (Some [::t])] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::t; t; T_num T_i32] /\ t2s = ts ++ [::t].
Qed. *)

Lemma Select_typing_Some_nil: forall C t1s t2s,
    be_typing C [::BI_select (Some [::])] (Tf t1s t2s) ->
    False.
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //.
  - rewrite -(cat0s [:: BI_select (Some [::])]) in Econs.
    apply concat_cancel_last in Econs. destruct Econs.
    subst. eapply IHHType2 => //=.
  - eapply IHHType => //=.
Qed.

Lemma Select_typing_Some_ext: forall C t1s t2s t t',
    be_typing C [::BI_select (Some (t :: t'))] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::t; t; T_num T_i32] /\ t2s = ts ++ [::t].
Proof.
  move => C t1s t2s t t' HType.
  gen_ind_subst HType => //.
  - by exists [::].
  - apply extract_list1 in Econs; destruct Econs; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    edestruct H as [-> ->].
    exists (ts ++ x). by split; repeat rewrite -catA.
Qed.

Lemma Select_typing_Some: forall C t1s t2s t',
    be_typing C [::BI_select (Some t')] (Tf t1s t2s) ->
    exists ts t, t1s = ts ++ [::t; t; T_num T_i32] /\ t2s = ts ++ [::t].
Proof.
  move => C t1s t2s t' HType.
  gen_ind_subst HType => //.
  - by exists [::], t.
  - apply extract_list1 in Econs; destruct Econs; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    edestruct H as [t [-> ->]].
    exists (ts ++ x), t. by split; repeat rewrite -catA.
Qed.

Lemma Select_typing_None: forall C t1s t2s,
    be_typing C [::BI_select None] (Tf t1s t2s) ->
    exists ts t, is_numeric_type t
      /\ t1s = ts ++ [::t; t; T_num T_i32] /\ t2s = ts ++ [::t].
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //.
  - by exists [::], t.
  - apply extract_list1 in Econs; destruct Econs; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=; subst.
    edestruct H as [t [Hnumtype [-> ->]]].
    exists (ts ++ x), t. by split; repeat rewrite -catA.
Qed.

Lemma Block_typing: forall C bt es tn tm t1s t2s,
    be_typing C [::BI_block bt es] (Tf tn tm) ->
    expand_t C bt = Some (Tf t1s t2s) ->
    exists ts, tn = ts ++ t1s /\ tm = ts ++ t2s /\
      be_typing (upd_label C ([::t2s] ++ (tc_label C))) es (Tf t1s t2s).
Proof.
  move => C bt es tn tm t1s t2s HType HExp.
  dependent induction HType => //=.
  - rewrite H in HExp. inversion HExp. subst. by exists [::].
  - apply extract_list1 in x; destruct x; subst.
    eapply IHHType2; eauto.
    apply empty_typing in HType1. by subst.
  - edestruct IHHType => //=.
    destruct H as [t1s' [t2s' H]]. subst.
    exists (ts ++ x).
    repeat rewrite -catA.
    by repeat split => //=.
Qed.

Lemma Loop_typing: forall C bt es tn tm t1s t2s,
    be_typing C [::BI_loop bt es] (Tf tn tm) ->
    expand_t C bt = Some (Tf t1s t2s) ->
    exists ts, tn = ts ++ t1s /\ tm = ts ++ t2s /\
      be_typing (upd_label C ([::t1s] ++ (tc_label C))) es (Tf t1s t2s).
Proof.
  move => C bt es tn tm t1s t2s HType HExp.
  dependent induction HType => //=.
  - rewrite H in HExp. inversion HExp. subst. by exists [::].
  - apply extract_list1 in x; destruct x; subst.
    eapply IHHType2; eauto.
    apply empty_typing in HType1. by subst.
  - edestruct IHHType => //=.
    destruct H as [t1s' [t2s' H]]. subst.
    exists (ts ++ x).
    repeat rewrite -catA.
    by repeat split => //=.
Qed.

Lemma If_typing: forall C bt e1s e2s tn tm t1s t2s,
    be_typing C [::BI_if bt e1s e2s] (Tf tn tm) ->
    expand_t C bt = Some (Tf t1s t2s) ->
    exists ts0, tn = ts0 ++ t1s ++ [::T_num T_i32] /\ tm = ts0 ++ t2s /\
      be_typing (upd_label C ([:: t2s] ++ tc_label C)) e1s (Tf t1s t2s) /\
      be_typing (upd_label C ([:: t2s] ++ tc_label C)) e2s (Tf t1s t2s).
Proof.
  move => C bt e1s e2s tn tm t1s t2s HType HExp.
  gen_ind_subst HType.
  - rewrite H in HExp. inversion HExp. subst. by exists [::].
  - apply extract_list1 in H2; destruct H2; subst.
    eapply IHHType2; eauto.
    apply empty_typing in HType1. by subst.
  - edestruct IHHType => //=; subst => //=.
    destruct H as [t1s' [t2s' [H H']]]. subst.
    exists (ts ++ x).
    repeat rewrite -catA.
    repeat split => //=.
Qed.

Lemma Break_typing: forall n C t1s t2s,
    be_typing C [::BI_br n] (Tf t1s t2s) ->
    exists ts ts0, (N.to_nat n) < size (tc_label C) /\
               (* plop2 C n ts /\ *)
               lookup_N (tc_label C) (n) = Some ts /\
               t1s = ts0 ++ ts.
Proof.
  move => n C t1s t2s HType.
  dependent induction HType => //=.
  - (* by exists ts, t1s0. *) exists ts, t1s0.
    split.
    assert (lookup_N (tc_label C) n <> None) as H'.
    rewrite H => //=.
    apply lookup_N_Some in H'.
    rewrite length_is_size in H' => //=.
    split => //=.
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [ts0 [H1 [H2 H3]]]. subst.
    exists x, (ts ++ ts0).
    repeat split => //=.
    by rewrite -catA.
Qed.

(*
Lemma Br_if_typing: forall C ts1 ts2 i,
be_typing C [::BI_br_if i] (Tf ts1 ts2) ->
exists ts ts', ts2 = ts ++ ts' /\ ts1 = ts2 ++ [::T_num T_i32] /\ i < length (tc_label C) /\ plop2 C i ts'.
*)
(* Is removal of (N.to_nat i < length (tc_label C)) result okay?
   Similar removal implicit in Br_table_typing by gen_ind_subst hypothesis
    Also seen in (globals_agree -> globali_agree)?
*)
Lemma Br_if_typing: forall C ts1 ts2 i,
    be_typing C [::BI_br_if i] (Tf ts1 ts2) ->
    exists ts ts', ts2 = ts ++ ts' /\ ts1 = ts2 ++ [::T_num T_i32]
      (*/\ N.to_nat i < length (tc_label C)*) /\ lookup_N (tc_label C) i = Some ts'.
Proof.
  move => C ts1 ts2 i HType.
  gen_ind_subst HType.
  - exists [::], ts2. repeat split.
    (* N.to_nat i0 < length (tc_label C0) evident from lookup yielding Some ts2 *)
    apply H.
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - rewrite -catA. f_equal => //=.
    edestruct IHHType => //=.
    destruct H as [ts' [H1 [H2 (*[H3 H4]*)H4]]].
    exists (ts ++ x), ts'. subst.
    split.
    + repeat rewrite -catA. by f_equal.
    + split => //=.
Qed.

(*
Lemma Br_table_typing: forall C ts1 ts2 ids i0,
    be_typing C [::BI_br_table ids i0] (Tf ts1 ts2) ->
    exists ts1' ts, ts1 = ts1' ++ ts ++ [::T_i32] /\
                         all (fun i => (i < length (tc_label C)) && (plop2 C i ts)) (ids ++ [::i0]).
*)
Lemma Br_table_typing: forall C ts1 ts2 ids i0,
    be_typing C [::BI_br_table ids i0] (Tf ts1 ts2) ->
    exists ts1' ts, ts1 = ts1' ++ ts ++ [::T_num T_i32]
      /\ List.Forall (fun i : N => lookup_N (tc_label C) i = Some ts) (ids ++ [::i0]).
Proof.
  move => C ts1 ts2 ids i0 HType.
  gen_ind_subst HType.
  - by exists t1s, ts.
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [ts' [H1 H2]].
    exists (ts ++ x), ts'. subst.
    split => //=.
    + repeat rewrite -catA. by f_equal => //=.
Qed.

Lemma Return_typing: forall C t1s t2s,
    be_typing C [::BI_return] (Tf t1s t2s) ->
    exists ts ts', t1s = ts' ++ ts /\
                   tc_return C = Some ts.
Proof.
  move => C t1s t2s HType.
  dependent induction HType => //=.
  - by exists ts, t1s0.
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [ts' [H1 H2]]. subst.
    exists x, (ts ++ ts').
    split => //=.
    by rewrite -catA.
Qed.

Lemma Call_typing: forall j C t1s t2s,
  be_typing C [::BI_call j] (Tf t1s t2s) ->
  exists ts t1s' t2s', (*j < length (tc_func C) /\*)
  lookup_N (tc_func C) j = Some (Tf t1s' t2s') /\
                      t1s = ts ++ t1s' /\
                      t2s = ts ++ t2s'.
Proof.
  move => j C t1s t2s HType.
  dependent induction HType; subst => //=.
  - exists [::], t1s, t2s. split => //=.
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [t1s' [t2s' [H1 [H2 H3]]]].
    subst.
    exists (ts ++ x), t1s', t2s'.
    repeat rewrite -catA.
    by repeat (split => //=).
Qed.

Lemma Call_indirect_typing: forall x y C t1s t2s,
  be_typing C [::BI_call_indirect x y] (Tf t1s t2s) ->
  exists tn tm ts tabt, (*tc_table C <> nil /\ i < length (tc_type C) /\*)
  lookup_N (tc_table C) x = Some tabt /\
  tabt.(tt_elem_type) = T_funcref /\
  lookup_N (tc_type C) y = Some (Tf tn tm) /\
  t1s = ts ++ tn ++ [::T_num T_i32] /\ t2s = ts ++ tm.
Proof.
  move => x y C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t1s0, t2s, [::], tabtype.
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by apply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [tm [ts' [tabtype [H1 [H2 [H3 [H4 H5]]]]]]]. subst.
    exists x0, tm, (ts ++ ts'), tabtype.
    by repeat rewrite -catA.
Qed.

Lemma Local_tee_typing: forall C i ts1 ts2,
    be_typing C [::BI_local_tee i] (Tf ts1 ts2) ->
    exists ts t, ts1 = ts2 /\ ts1 = ts ++ [::t]
      /\ lookup_N (tc_local C) i = Some t.
Proof.
  move => C i ts1 ts2 HType.
  gen_ind_subst HType.
  - exists [::], t. repeat split. apply H.
  - apply extract_list1 in H1; destruct H1; subst.
    apply empty_typing in HType1; subst.
    by eapply IHHType2 => //=.
  - edestruct IHHType => //=.
    destruct H as [t [H1 [H2 H3]]]. subst.
    exists (ts ++ x), t. subst.
    repeat (try split => //=).
    by rewrite -catA.
Qed.

Lemma Local_tee_typing_e: forall s C i ts1 ts2,
    e_typing s C [::AI_basic (BI_local_tee i)] (Tf ts1 ts2) ->
    exists ts t, ts1 = ts2 /\ ts1 = ts ++ [::t]
      /\ lookup_N (tc_local C) i = Some t.
Proof.
  move => s C i ts1 ts2 HType.
  apply et_to_bet in HType;
    last by unfold es_is_basic, e_is_basic;
    apply List.Forall_cons; eauto.
  apply Local_tee_typing in HType.
  destruct HType as [ts [t [H1 [H2 H3]]]].
  by exists ts, t.
Qed.

Lemma Local_get_typing: forall C i t1s t2s,
    be_typing C [::BI_local_get i] (Tf t1s t2s) ->
    exists t, lookup_N (tc_local C) i = Some t /\
    t2s = t1s ++ [::t].
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 H2]. subst.
    exists x.
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Local_set_typing: forall C i t1s t2s,
    be_typing C [::BI_local_set i] (Tf t1s t2s) ->
    exists t, lookup_N (tc_local C) i = Some t /\
    t1s = t2s ++ [::t].
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 H2]. subst.
    exists x.
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Global_get_typing: forall C i t1s t2s,
    be_typing C [::BI_global_get i] (Tf t1s t2s) ->
    exists t, option_map tg_t (lookup_N (tc_global C) i) = Some t /\
    t2s = t1s ++ [::t].
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 H2]. subst.
    exists x.
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Global_set_typing: forall C i t1s t2s,
    be_typing C [::BI_global_set i] (Tf t1s t2s) ->
    exists g t, lookup_N (tc_global C) i = Some g /\
    tg_t g = t /\
    is_mut g /\
    t1s = t2s ++ [::t].
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists g, (tg_t g).
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [t [H1 [H2 [H3 H4]]]]. subst.
    exists x, (tg_t x).
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Table_get_typing: forall C i t1s t2s,
    be_typing C [::BI_table_get i] (Tf t1s t2s) ->
    exists tabtype t ts, lookup_N (tc_table C) i = Some tabtype /\
    tt_elem_type tabtype = t /\
    t1s = ts ++ [::T_num T_i32] /\ t2s = ts ++ [:: T_ref t].
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists tabtype, (tt_elem_type tabtype), [::].
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [t' [ts' [H1 [H2 [H3 H4]]]]]. subst.
    exists x, (tt_elem_type x), (ts ++ ts').
    repeat split => //=;
    by rewrite -catA.
Qed.

Lemma Table_set_typing: forall C i t1s t2s,
    be_typing C [::BI_table_set i] (Tf t1s t2s) ->
    exists tabtype t, lookup_N (tc_table C) i = Some tabtype /\
    tt_elem_type tabtype = t /\
    t1s = t2s ++ [::T_num T_i32; T_ref t].
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists tabtype, (tt_elem_type tabtype).
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [t' [H1 [H2 H3]]]. subst.
    exists x, (tt_elem_type x).
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Table_size_typing: forall C i t1s t2s,
  be_typing C [::BI_table_size i] (Tf t1s t2s) ->
  exists tabtype, lookup_N (tc_table C) i = Some tabtype /\
  t2s = t1s ++ [::T_num T_i32].
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists tabtype.
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 H2]. subst.
    exists x.
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Table_grow_typing: forall C i t1s t2s,
  be_typing C [::BI_table_grow i] (Tf t1s t2s) ->
  exists tabtype t ts, lookup_N (tc_table C) i = Some tabtype /\
  tt_elem_type tabtype = t /\
  t1s = ts ++ [::T_ref t; T_num T_i32] /\ t2s = ts ++ [::T_num T_i32].
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists tabtype, (tt_elem_type tabtype), [::].
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [t' [ts' [H1 [H2 [H3 H4]]]]]. subst.
    exists x, (tt_elem_type x), (ts ++ ts').
    repeat split => //=;
    by rewrite -catA.
Qed.

Lemma Table_fill_typing: forall C i t1s t2s,
  be_typing C [::BI_table_fill i] (Tf t1s t2s) ->
  exists tabtype t, lookup_N (tc_table C) i = Some tabtype /\
  tt_elem_type tabtype = t /\
  t1s = t2s ++ [::T_num T_i32; T_ref t; T_num T_i32].
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists tabtype, (tt_elem_type tabtype).
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [t' [H1 [H2 H3]]]. subst.
    exists x, (tt_elem_type x).
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Table_copy_typing: forall C x y t1s t2s,
  be_typing C [::BI_table_copy x y] (Tf t1s t2s) ->
  exists tabtype1 tabtype2 t, lookup_N (tc_table C) x = Some tabtype1 /\
  lookup_N (tc_table C) y = Some tabtype2 /\
  tt_elem_type tabtype1 = t /\
  tt_elem_type tabtype2 = t /\
  t1s = t2s ++ [::T_num T_i32; T_num T_i32; T_num T_i32].
Proof.
  move => C x y t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists tabtype1, tabtype2, (tt_elem_type tabtype1).
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [x0' [t' [H1 [H2 [H3 [H4 H5]]]]]]. subst.
    exists x0, x0', (tt_elem_type x0).
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Table_init_typing: forall C x y t1s t2s,
  be_typing C [::BI_table_init x y] (Tf t1s t2s) ->
  exists tabtype t, lookup_N (tc_table C) x = Some tabtype /\
  tt_elem_type tabtype = t /\
  lookup_N (tc_elem C) y = Some t /\
  t1s = t2s ++ [::T_num T_i32; T_num T_i32; T_num T_i32].
Proof.
  move => C x y t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists tabtype, (tt_elem_type tabtype).
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [t' [H1 [H2 [H3 ]]]]. subst.
    exists x0, (tt_elem_type x0).
    repeat split => //=.
    by rewrite -catA.
Qed.

Lemma Elem_drop_typing: forall C i t1s t2s,
    be_typing C [::BI_elem_drop i] (Tf t1s t2s) ->
    exists t, lookup_N (tc_elem C) i = Some t /\
    t2s = t1s.
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 H2]. subst.
    exists x.
    repeat split => //=.
Qed.

Lemma Load_typing: forall C t a off tp_sx t1s t2s,
    be_typing C [::BI_load t tp_sx a off] (Tf t1s t2s) ->
    exists ts, t1s = ts ++ [::T_num T_i32] /\ t2s = ts ++ [::T_num t] /\
                    tc_memory C <> nil /\
                    load_store_t_bounds a (option_projl tp_sx) t.
Proof.
  move => C t a off tp_sx t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::].
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 [H3 H4]]]. subst.
    exists (ts ++ x).
    by repeat rewrite -catA.
Qed.

Lemma Store_typing: forall C t a off tp t1s t2s,
    be_typing C [::BI_store t tp a off] (Tf t1s t2s) ->
    t1s = t2s ++ [::T_num T_i32; T_num t] /\
    tc_memory C <> nil /\
    load_store_t_bounds a tp t.
Proof.
  move => C t a off tp t1s t2s HType.
  dependent induction HType; subst => //=.
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by eapply IHHType2.
  - edestruct IHHType => //=. subst.
    by repeat rewrite -catA.
Qed.

Lemma Memory_size_typing: forall C t1s t2s,
    be_typing C [::BI_memory_size] (Tf t1s t2s) ->
    tc_memory C <> nil /\ t2s = t1s ++ [::T_num T_i32].
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by eapply IHHType2.
  - edestruct IHHType => //=. subst.
    by repeat rewrite -catA.
Qed.

Lemma Memory_grow_typing: forall C t1s t2s,
    be_typing C [::BI_memory_grow] (Tf t1s t2s) ->
    exists ts, tc_memory C <> nil /\ t2s = t1s /\ t1s = ts ++ [::T_num T_i32].
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists [::].
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst.
    exists (ts ++ x).
    by repeat rewrite -catA.
Qed.

Lemma Memory_fill_typing: forall C t1s t2s,
    be_typing C [::BI_memory_fill] (Tf t1s t2s) ->
    tc_memory C <> nil /\
    t1s = t2s ++ [::T_num T_i32; T_num T_i32; T_num T_i32].
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by eapply IHHType2.
  - edestruct IHHType => //=. subst.
    by repeat rewrite -catA.
Qed.

Lemma Memory_copy_typing: forall C t1s t2s,
    be_typing C [::BI_memory_copy] (Tf t1s t2s) ->
    tc_memory C <> nil /\
    t1s = t2s ++ [::T_num T_i32; T_num T_i32; T_num T_i32].
Proof.
  move => C t1s t2s HType.
  dependent induction HType; subst => //=.
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by eapply IHHType2.
  - edestruct IHHType => //=. subst.
    by repeat rewrite -catA.
Qed.

Lemma Memory_init_typing: forall C i t1s t2s,
    be_typing C [::BI_memory_init i] (Tf t1s t2s) ->
    tc_memory C <> nil /\
    N.to_nat i < length (tc_data C) /\
    t1s = t2s ++ [::T_num T_i32; T_num T_i32; T_num T_i32].
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by eapply IHHType2.
  - edestruct IHHType => //=.
    destruct H0 as [H1 H2]. subst.
    repeat split => //=.
    by repeat rewrite -catA.
Qed.

Lemma Data_drop_typing: forall C i t1s t2s,
    be_typing C [::BI_data_drop i] (Tf t1s t2s) ->
    exists t, lookup_N (tc_data C) i = Some t /\
    t1s = t2s.
Proof.
  move => C i t1s t2s HType.
  dependent induction HType; subst => //=.
  - by exists t.
  - apply extract_list1 in x. destruct x. subst.
    apply empty_typing in HType1. subst.
    by apply IHHType2.
  - edestruct IHHType => //=.
    destruct H as [H1 H2]. subst.
    exists x.
    repeat split => //=.
Qed.

(*
  Unlike the above proofs which have a linear dependent structure therefore hard
    to factorize into a tactic, the following proofs are independent of each other
    and should therefore be easily refactorable.
*)

(* split to assist debugging *)
Ltac invert_be_typing_step:=
  lazymatch goal with
  | H: (?es ++ [::?e])%list = [::_] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _; _] |- _ =>
    extract_listn
  | H: (?es ++ [::?e])%list = [::_; _; _; _] |- _ =>
    extract_listn
  | H: be_typing _ [::] _ |- _ =>
    apply empty_typing in H; subst
  | H: be_typing _ [:: BI_const_num _] _ |- _ =>
    apply BI_const_num_typing in H; subst
  | H: be_typing _ [:: BI_const_vec _] _ |- _ =>
    apply BI_const_vec_typing in H; subst
  | H: be_typing _ [:: BI_ref_null _] _ |- _ =>
    apply BI_ref_null_typing in H; subst
  | H: be_typing _ [:: BI_ref_func _] _ |- _ =>
    let tf := fresh "tf" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    apply BI_ref_func_typing in H; destruct H as [tf [H1 [H2 H3]]]; subst
  | H: be_typing _ [:: BI_const_num _; BI_const_num _] _ |- _ =>
    apply BI_const2_nn_typing in H; subst
  | H: be_typing _ [:: BI_const_vec _; BI_const_vec _] _ |- _ =>
    apply BI_const2_vv_typing in H; subst
  | H: be_typing _ [:: BI_ref_null _; BI_ref_null _] _ |- _ =>
    apply BI_const2_rr_typing in H; subst
  | H: be_typing _ [:: BI_const_num _; BI_const_num _; BI_const_num _] _ |- _ =>
    apply BI_const3_nnn_typing in H; subst
  | H: be_typing _ [:: BI_const_vec _; BI_const_vec _; BI_const_num _] _ |- _ =>
    apply BI_const3_vvn_typing in H; subst
  | H: be_typing _ [:: BI_ref_null _; BI_ref_null _; BI_const_num _] _ |- _ =>
    apply BI_const3_rrn_typing in H; subst
  (* | H: be_typing _ [:: BI_const_vec _; BI_const_vec _; BI_const_vec _] _ |- _ =>
    apply BI_const3_vvv_typing in H; subst *)
  | H: be_typing _ [::BI_unop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Unop_typing in H; destruct H as [H1 [ts H2]]; subst
  | H: be_typing _ [::BI_binop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Binop_typing in H; destruct H as [H1 [ts H2]]; subst
  | H: be_typing _ [::BI_testop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Testop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::BI_relop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Relop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::BI_cvtop _ _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Cvtop_typing in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::BI_ref_is_null] _ |- _ =>
    let ts := fresh "ts" in
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Ref_is_null_typing in H; destruct H as [ts [t [H1 H2]]]; subst
  | H: be_typing _ [::BI_drop] _ |- _ =>
    apply Drop_typing in H; destruct H; subst
  | H: be_typing _ [::BI_select (Some [::])] _ |- _ =>
    apply Select_typing_Some_nil in H; destruct H
  | H: be_typing _ [::BI_select (Some _)] _ |- _ =>
    let ts := fresh "ts" in
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Select_typing_Some in H; destruct H as [ts [H1 H2]]; subst
  | H: be_typing _ [::BI_select None] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    apply Select_typing_None in H; destruct H as [ts [t [H1 [H2 H3]]]]; subst
  | H: be_typing _ [::BI_block _ _] _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let t2s := fresh "t2s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    apply Block_typing in H; destruct H as [ts [H1 [H2 H3]]]; subst
  | H: be_typing _ [::BI_loop _ _] _ |- _ =>
    let ts := fresh "ts" in
    let t1s := fresh "t1s" in
    let t2s := fresh "t2s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    apply Loop_typing in H; destruct H as [ts [H1 [H2 H3]]]; subst
  | H: be_typing _ [::BI_if _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply If_typing in H; destruct H as [ts [H1 [H2 [H3 H4]]]]; subst
  | H: be_typing _ [::BI_br_if _] _ |- _ =>
    let ts := fresh "ts" in
    let ts' := fresh "ts'" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Br_if_typing in H; destruct H as [ts [ts' [H1 [H2 H3]]]]; subst
  | H: be_typing _ [::BI_br_table _ _] _ |- _ =>
    let ts := fresh "ts" in
    let ts' := fresh "ts'" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Br_table_typing in H; destruct H as [ts [ts' [H1 H2]]]; subst
  | H: be_typing _ [::BI_local_tee _] _ |- _ =>
    let ts := fresh "ts" in
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Local_tee_typing in H; destruct H as [ts [t [H1 [H2 H3]]]]; subst
  | H: be_typing _ [::BI_local_get _] _ |- _ =>
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Local_get_typing in H; destruct H as [t [H1 H2]]; subst
  | H: be_typing _ [::BI_local_set _] _ |- _ =>
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Local_set_typing in H; destruct H as [t [H1 H2]]; subst
  | H: be_typing _ [::BI_global_get _] _ |- _ =>
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Global_get_typing in H; destruct H as [t [H1 H2]]; subst
  | H: be_typing _ [::BI_global_set _] _ |- _ =>
    let g := fresh "g" in
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Global_set_typing in H; destruct H as [g [t [H1 [H2 [H3 H4]]]]]; subst
  | H: be_typing _ [::BI_table_get _] _ |- _ =>
    let ttype := fresh "ttype" in
    let t := fresh "t" in
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Table_get_typing in H; destruct H as [ttype [t [ts [H1 [H2 [H3 H4]]]]]]; subst
  | H: be_typing _ [::BI_table_set _] _ |- _ =>
    let ttype := fresh "ttype" in
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    apply Table_set_typing in H; destruct H as [ttype [t [H1 [H2 H3]]]]; subst
  | H: be_typing _ [::BI_table_size _] _ |- _ =>
    let ttype := fresh "ttype" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Table_size_typing in H; destruct H as [ttype [H1 H2]]; subst
  | H: be_typing _ [::BI_table_grow _] _ |- _ =>
    let ttype := fresh "ttype" in
    let t := fresh "t" in
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Table_grow_typing in H; destruct H as [ttype [t [ts [H1 [H2 [H3 H4]]]]]]; subst
  | H: be_typing _ [::BI_table_fill _] _ |- _ =>
    let ttype := fresh "ttype" in
    let t := fresh "t" in
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Table_fill_typing in H; destruct H as [ttype [t [H1 [H2 H3]]]]; subst
  | H: be_typing _ [::BI_table_copy _ _] _ |- _ =>
    let ttype := fresh "ttype" in
    let t := fresh "t" in
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    let H5 := fresh "H5" in
    apply Table_copy_typing in H; destruct H as [ttype [t [ts [H1 [H2 [H3 [H4 H5]]]]]]]; subst
  | H: be_typing _ [::BI_table_init _ _] _ |- _ =>
    let ttype := fresh "ttype" in
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Table_init_typing in H; destruct H as [ttype [t [H1 [H2 [H3 H4]]]]]; subst
  | H: be_typing _ [::BI_elem_drop _] _ |- _ =>
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Elem_drop_typing in H; destruct H as [t [H1 H2]]; subst
  | H: be_typing _ [::BI_load _ _ _ _] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Load_typing in H; destruct H as [ts [H1 [H2 [H3 H4]]]]; subst
  | H: be_typing _ [::BI_store _ _ _ _] _ |- _ =>
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    apply Store_typing in H; destruct H as [H1 [H2 H3]]; subst
  | H: be_typing _ [::BI_memory_size] _ |- _ =>
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Memory_size_typing in H; destruct H as [H1 H2]; subst
  | H: be_typing _ [::BI_memory_grow] _ |- _ =>
    let ts := fresh "ts" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply Memory_grow_typing in H; destruct H as [ts [H1 [H2 H3]]]; subst
  | H: be_typing _ [::BI_memory_fill] _ |- _ =>
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Memory_fill_typing in H; destruct H as [H1 H2]; subst
  | H: be_typing _ [::BI_memory_copy] _ |- _ =>
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Memory_copy_typing in H; destruct H as [H1 H2]; subst
  | H: be_typing _ [::BI_memory_init _] _ |- _ =>
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    apply Memory_init_typing in H; destruct H as [H1 [H2 H3 ]]; subst
  | H: be_typing _ [::BI_data_drop _] _ |- _ =>
    let t := fresh "t" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply Data_drop_typing in H; destruct H as [t [H1 H2]]; subst
  | H: be_typing _ (_ ++ _) _ |- _ =>
    let ts1 := fresh "ts1" in
    let ts2 := fresh "ts2" in
    let ts3 := fresh "ts3" in
    let ts4 := fresh "ts4" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    apply composition_typing in H; destruct H as [ts1 [ts2 [ts3 [ts4 [H1 [H2 [H3 H4]]]]]]]
  | H: be_typing _ [::_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: be_typing _ [::_;_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: be_typing _ [::_;_;_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: _ ++ [::_] = _ ++ [::_] |- _ =>
    apply concat_cancel_last in H; destruct H; subst
  end.
Ltac invert_be_typing:=
  repeat invert_be_typing_step.

Lemma app_binop_num_type_preserve: forall op v1 v2 v,
  app_binop_num op v1 v2 = Some v ->
  typeof_num v = typeof_num v1.
Proof.
  move => op v1 v2 v Hbinop.
  unfold app_binop_num in Hbinop.
  destruct op as [op | op]; destruct v1 as [c1|c1|c1|c1]; destruct v2 as [c2|c2|c2|c2] => //.
  1,2: remember (app_binop_i op c1 c2) as vo.
  3,4: remember (app_binop_f op c1 c2) as vo.
  all: destruct vo; rewrite - Heqvo in Hbinop; simpl in Hbinop; by inversion Hbinop => //.
Qed.

Lemma app_binop_type_preserve: forall op v1 v2 v,
  app_binop op v1 v2 = Some v ->
  typeof v = typeof v1.
Proof.
  move => op v1 v2 v Hbinop.
  unfold app_binop in Hbinop.
  destruct op as [op | op];
  destruct v1 as [[c1|c1|c1|c1]|[c1]|[c1|c1|c1]] => //;
  destruct v2 as [[c2|c2|c2|c2]|[c2]|[c2|c2|c2]] => //;
  unfold app_binop_num in Hbinop.
  1,2: remember (app_binop_i op c1 c2) as vo.
  3,4: remember (app_binop_f op c1 c2) as vo.
  all: destruct vo; rewrite - Heqvo in Hbinop; simpl in Hbinop; by inversion Hbinop => //.
Qed.

Lemma t_Unop_num_preserve: forall C v t op be tf,
    be_typing C [:: BI_const_num v; BI_unop t op] tf ->
    reduce_simple (to_e_list [::BI_const_num v; BI_unop t op]) (to_e_list [::be]) ->
    be_typing C [::be] tf.
Proof.
  move => C v t op be tf HType HReduce.
  destruct tf as [ts1 ts2].
  inversion HReduce; b_to_a_revert; subst.
  invert_be_typing.
  rewrite catA.
  apply bet_weakening_empty_1.
  replace (typeof_num v) with (typeof_num (app_unop_num op v)); first by apply bet_const_num.
  by destruct op; destruct v.
Qed.

(* Unop (and most operations) only accepts num values,
    so the rest are redundant due to having a false premise *)

Lemma t_Binop_preserve_success: forall C v1 v2 t op be tf,
    be_typing C [:: BI_const_num v1; BI_const_num v2; BI_binop t op] tf ->
    reduce_simple (to_e_list [::BI_const_num v1; BI_const_num v2; BI_binop t op]) (to_e_list [::be]) ->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 t op be tf HType HReduce.
  destruct tf as [ts1 ts2].
  inversion HReduce; b_to_a_revert; subst.
  invert_be_typing.
  rewrite catA in H1. apply concat_cancel_last in H1. destruct H1; subst.
  repeat rewrite catA.
  apply bet_weakening_empty_1.
  apply app_binop_num_type_preserve in H0.
  rewrite -H1. rewrite -H0.
  by apply bet_const_num.
Qed.

(* It seems very hard to refactor the i32 and i64 cases into one because of
     the polymorphism of app_testop_i. *)
Lemma t_Testop_i32_preserve: forall C c testop tf,
    be_typing C [::BI_const_num (VAL_int32 c); BI_testop T_i32 testop] tf ->
    be_typing C [::BI_const_num (VAL_int32 (wasm_bool (app_testop_i testop c)))] tf.
Proof.
  move => C c testop tf HType.
  gen_ind_subst HType.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1. simpl.
    apply bet_const_num.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType.
Qed.

Lemma t_Testop_i64_preserve: forall C c testop tf,
    be_typing C [::BI_const_num (VAL_int64 c); BI_testop T_i64 testop] tf ->
    be_typing C [::BI_const_num (VAL_int32 (wasm_bool (app_testop_i testop c)))] tf.
Proof.
  move => C c testop tf HType.
  gen_ind_subst HType.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1. simpl.
    by apply bet_const_num.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType.
Qed.

Lemma t_Relop_preserve: forall C v1 v2 t be op tf,
    be_typing C [::BI_const_num v1; BI_const_num v2; BI_relop t op] tf ->
    reduce_simple [:: AI_basic (BI_const_num v1); AI_basic (BI_const_num v2); AI_basic (BI_relop t op)] [::AI_basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 t be op tf HType HReduce.
  destruct tf as [ts1 ts2].
  inversion HReduce; subst.
  invert_be_typing.
  replace ([::T_num t;T_num t]) with ([::T_num t] ++ [::T_num t]) in H2 => //.
  rewrite catA in H2.
  apply concat_cancel_last in H2. destruct H2 as [H3 H4]. subst.
  rewrite catA in H1.
  apply concat_cancel_last in H1. destruct H1 as [H5 H6]. subst.
  repeat rewrite catA.
  apply bet_weakening_empty_1.
  by apply bet_const_num.
Qed.

Lemma typeof_deserialise: forall v t,
  typeof_num (wasm_deserialise v t) = t.
Proof.
  move=> v. by case. (* destruct and unfold on t *)
Qed.

Lemma be_typing_const_deserialise: forall C v t,
    be_typing C [:: BI_const_num (wasm_deserialise (bits v) t)] (Tf [::] [::T_num t]).
Proof.
  move => C v t.
  assert (be_typing C [:: BI_const_num (wasm_deserialise (bits v) t)] (Tf [::] [:: T_num (typeof_num (wasm_deserialise (bits v) t))])); first by apply bet_const_num.
  by rewrite typeof_deserialise in H.
Qed.

Lemma t_Convert_preserve: forall C v t1 t2 sx be tf,
    be_typing C [::BI_const_num v; BI_cvtop t2 CVO_convert t1 sx] tf ->
    reduce_simple [::AI_basic (BI_const_num v); AI_basic (BI_cvtop t2 CVO_convert t1 sx)] [::AI_basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v t1 t2 sx be tf HType HReduce.
  inversion HReduce; subst. rename H5 into E.
  gen_ind_subst HType.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1.
    by destruct t2; simpl in E;
      match type of E with
        option_map _ ?e = _ => destruct e eqn:HDestruct => //=
      end; inversion E; apply bet_const_num.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType; eauto.
Qed.

(* rs_reinterpret :
  forall t1 t2 v,
    types_agree (T_num t1) (VAL_num v) ->
    reduce_simple [::$VAN v; AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] [::$VAN (wasm_deserialise (bits v) t2)]
*)
Lemma t_Reinterpret_preserve: forall C v t1 t2 be tf,
    be_typing C [::BI_const_num v; BI_cvtop t2 CVO_reinterpret t1 None] tf ->
    reduce_simple [::AI_basic (BI_const_num v); AI_basic (BI_cvtop t2 CVO_reinterpret t1 None)] [::AI_basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C v t1 t2 be tf HType HReduce.
  inversion HReduce; subst.
  gen_ind_subst HType.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1.
    apply be_typing_const_deserialise.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType; eauto.
Qed.

(* will never work due to the false case having AI refs *)
Lemma t_Ref_is_null_false_preserve_be: forall C ref tf,
  be_typing C [:: to_b_single (v_to_e (VAL_ref ref)); BI_ref_is_null] tf ->
  reduce_simple [:: v_to_e (VAL_ref ref); AI_basic BI_ref_is_null] [:: $VAN VAL_int32 Wasm_int.Int32.zero] ->
  False.
Proof.
  intros C ref tf HType HReduce.
  destruct tf as [ts1 ts2].
  invert_be_typing.
  inversion HReduce; subst.
  destruct ref, ref0; simpl in * => //=;
  clear H; invert_be_typing; simpl in * => //=.
  by destruct (H0 r0).
Qed.

Lemma t_Ref_is_null_false_preserve: forall s C ref tf,
  e_typing s C [:: v_to_e (VAL_ref ref); AI_basic BI_ref_is_null] tf ->
  reduce_simple [:: v_to_e (VAL_ref ref); AI_basic BI_ref_is_null] [:: $VAN VAL_int32 Wasm_int.Int32.zero] ->
  e_typing s C [:: $VAN VAL_int32 Wasm_int.Int32.zero] tf.
Proof.
  intros s C ref tf HType HReduce.
  destruct tf as [ts1 ts2].
  rewrite -cat1s in HType.
  apply e_composition_typing in HType.
  destruct HType as [ts [t1s' [t2s' [t3s [H1 [H2 [H3 H4]]]]]]].
  subst.
  apply et_to_bet in H4;
    last by unfold es_is_basic, e_is_basic;
    apply List.Forall_cons => //; eauto.
  simpl in H4. invert_be_typing.
  destruct ref => //=; simpl in H3;
  [ apply AI_ref_null_typing in H3
  | apply AI_ref_func_typing in H3;
    destruct H3 as [_ [_ H3]]
  | apply AI_ref_extern_typing in H3 ];
  simpl in H3; apply concat_cancel_last in H3;
  destruct H3; subst; repeat apply ety_weakening;
  apply et_weakening_empty_1; apply ety_a' => //; simpl;
  try (
    unfold es_is_basic, e_is_basic;
    apply List.Forall_cons => //; eauto
  ); apply bet_const_num.
Qed.

Lemma t_Ref_is_null_true_preserve_be: forall C ref tf,
  be_typing C [:: BI_ref_null ref; BI_ref_is_null] tf ->
  reduce_simple (to_e_list [:: BI_ref_null ref; BI_ref_is_null]) [:: $VAN VAL_int32 Wasm_int.Int32.one] ->
  be_typing C [:: $VBN VAL_int32 Wasm_int.Int32.one] tf.
Proof.
  move => C ref tf HType HReduce.
  gen_ind_subst HType.
  - (* Composition *)
    invert_be_typing.
    apply bet_weakening_empty_1.
    apply bet_const_num.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType; eauto.
Qed.

Lemma t_Drop_preserve: forall C v tf,
  be_typing C [:: to_b_single (v_to_e v); BI_drop] tf ->
  be_typing C [::] tf.
Proof.
  move => C v tf HType.
  destruct v as [| |[]] => //=;
  gen_ind_subst HType;
  try (invert_be_typing; apply bet_weakening_empty_both; apply bet_empty);
  try (apply bet_weakening; by eapply IHHType).
Qed.

Ltac destruct_ands :=
  repeat lazymatch goal with
  | H: _ /\ _ |- _ =>
    destruct H; subst
  end.

Ltac auto_concat_cancel_last_step:=
  lazymatch goal with
  | H: _ ++ [::_] = _ ++ [::_] |- _ =>
    apply concat_cancel_last in H; destruct H; subst
  | H: [::?a] = _ ++ [::?b] |- _ =>
    rewrite -(cat0s [::a]) in H;
    apply concat_cancel_last in H; destruct H; subst

  | H: _ ++ [::_] = _ ++ [::?a; ?b] |- _ =>
    rewrite -(cat1s a [::b]) in H
  | H: _ ++ [::_] = _ ++ [::?a; ?b; ?c] |- _ =>
    rewrite -(cat1s a [::b; c]) in H
  | H: _ ++ [::_] = ?a ++ ?b ++ [::?c] |- _ =>
    rewrite (catA a b [::c]) in H
  | H: _ ++ [::_] = ?a ++ ?b ++ ?c ++ [::?d] |- _ =>
    rewrite (catA a b (c ++ [::d])) in H;
    rewrite (catA (a ++ b) c [::d]) in H
  | H: _ ++ [::_] = ?a ++ ?b ++ [::?c; ?d] |- _ =>
    rewrite (catA a b [::c; d]) in H

  | H: _ ++ [::?a; ?b] = _ ++ [::_] |- _ =>
    rewrite -(cat1s a [::b]) in H
  | H: _ ++ [::?a; ?b; ?c] = _ ++ [::_] |- _ =>
    rewrite -(cat1s a [::b; c]) in H
  | H: ?a ++ ?b ++ [::?c] = _ ++ [::_] |- _ =>
    rewrite (catA a b [::c]) in H
  | H: ?a ++ ?b ++ ?c ++ [::?d] = _ ++ [::_] |- _ =>
    rewrite (catA a b (c ++ [::d])) in H;
    rewrite (catA (a ++ b) c [::d]) in H
  | H: ?a ++ ?b ++ [::?c; ?d] = _ ++ [::_] |- _ =>
    rewrite (catA a b [::c; d]) in H
  end.
Ltac auto_concat_cancel_last:=
  repeat auto_concat_cancel_last_step.

(* same proof content for both, aside from intros and H5/H6 *)
Lemma t_Select_none_preserve: forall C v1 v2 be n tf,
    be_typing C [:: to_b_single (v_to_e v1); to_b_single (v_to_e v2); $VBN (VAL_int32 n); BI_select None] tf ->
    reduce_simple [:: v_to_e v1; v_to_e v2; $VAN (VAL_int32 n); AI_basic (BI_select None)] (to_e_list [:: be]) ->
    be_typing C [:: be] tf.
Proof.
  move => C v1 v2 be n tf HType HReduce.
  inversion HReduce; subst;
  destruct v1 as [| |[]] => //=;
  destruct v2 as [| |[]] => //=;
  rewrite H in H4 || rewrite H1 in H4; inversion H4;
  destruct tf; invert_be_typing; simpl in *;
  apply bet_weakening; auto_concat_cancel_last;
  (* repeat invert_be_typing for ref instructions to be discriminated *)
  invert_be_typing; simpl in *;
  auto_concat_cancel_last; try discriminate; simpl in *;
  repeat rewrite -catA; repeat apply bet_weakening; apply bet_weakening_empty_1;
  try constructor; try (rewrite H6; constructor).
Qed.
Lemma t_Select_some_preserve_nil: forall C v1 v2 n tf be,
    be_typing C [:: to_b_single (v_to_e v1); to_b_single (v_to_e v2); $VBN (VAL_int32 n); BI_select (Some [::])] tf ->
    reduce_simple [:: v_to_e v1; v_to_e v2; $VAN (VAL_int32 n); AI_basic (BI_select (Some [::]))] (to_e_list [:: be]) ->
    False.
Proof.
  move => C v1 v2 n tf be HType HReduce.
  inversion HReduce; subst;
  destruct v1 as [| |[]] => //=;
  destruct v2 as [| |[]] => //=;
  destruct tf; invert_be_typing.
Qed.
Lemma t_Select_some_preserve: forall C v1 v2 n t ts tf be,
    be_typing C [:: to_b_single (v_to_e v1); to_b_single (v_to_e v2); $VBN (VAL_int32 n); BI_select (Some (t :: ts))] tf ->
    reduce_simple [:: v_to_e v1; v_to_e v2; $VAN (VAL_int32 n); AI_basic (BI_select (Some (t :: ts)))] (to_e_list [:: be]) ->
    be_typing C [::be] tf.
Proof.
  move => C v1 v2 n t ts tf be HType HReduce.
  inversion HReduce; subst;
  destruct v1 as [| |[]] => //=;
  destruct v2 as [| |[]] => //=;
  rewrite H in H4 || rewrite H1 in H4; inversion H4;
  destruct tf; invert_be_typing; simpl in *;
  apply bet_weakening; auto_concat_cancel_last;
  (* repeat invert_be_typing for ref instructions to be discriminated *)
  invert_be_typing; simpl in *; destruct_ands;
  auto_concat_cancel_last; try discriminate; simpl in *;
  repeat rewrite -catA; repeat apply bet_weakening;
  apply bet_weakening_empty_1;
  try constructor; try (rewrite H3; constructor).
Qed.


Lemma t_Br_if_true_preserve: forall C c i tf,
  be_typing C [::BI_const_num (VAL_int32 c); BI_br_if i] tf ->
  reduce_simple (to_e_list [::BI_const_num (VAL_int32 c); BI_br_if i]) [::AI_basic (BI_br i)] ->
  be_typing C [::BI_br i] tf.
Proof.
  move => C c i tf HType HReduce.
  inversion HReduce; subst.
  gen_ind_subst HType => //=.
  - (* Composition *)
  invert_be_typing.
  apply (bet_br ts (ts ++ ts') H4).
  - (* Weakening *)
  apply bet_weakening.
  by eapply IHHType => //=.
Qed.

Lemma t_Br_if_false_preserve: forall C c i tf,
  be_typing C [::BI_const_num (VAL_int32 c); BI_br_if i] tf ->
  reduce_simple (to_e_list [::BI_const_num (VAL_int32 c); BI_br_if i]) [::] ->
  be_typing C [::] tf.
Proof.
  move => C c i tf HType HReduce.
  inversion HReduce; subst.
  gen_ind_subst HType => //=.
  - (* Composition *)
  invert_be_typing.
  apply bet_weakening_empty_both.
  by apply bet_empty.
  - (* Weakening *)
  apply bet_weakening.
  by eapply IHHType => //=.
Qed.

Lemma t_Br_table_preserve: forall C c ids i0 tf be,
    be_typing C [::BI_const_num (VAL_int32 c); BI_br_table ids i0] tf ->
    reduce_simple (to_e_list [::BI_const_num (VAL_int32 c); BI_br_table ids i0]) [::AI_basic be] ->
    be_typing C [::be] tf.
Proof.
  move => C c ids i0 tf be HType HReduce.
  inversion HReduce; subst.
  (* in range *)
  - dependent induction HType => //=.
    + (* Composition *)
      invert_be_typing.
      rewrite catA in H0. apply concat_cancel_last in H0. destruct H0. subst.
      move/List.Forall_forall in H2.
      assert (HInd: lookup_N (tc_label C) j = Some ts').
      -- apply H2. (* apply/inP. rewrite mem_cat. apply/orP. left. apply/inP. *)
        apply List.in_or_app. left. eapply List.nth_error_In. by eauto.
      remove_bools_options.
      by apply bet_br => //.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
  (* out of range *)
  - dependent induction HType => //=.
    + (* Composition *)
      invert_be_typing.
      rewrite catA in H1. apply concat_cancel_last in H1. destruct H1. subst.
      move/List.Forall_forall in H2.
      assert (HInd: lookup_N (tc_label C) i0 = Some ts').
      -- apply H2. (* apply/inP. apply/orP. right. *)
        apply List.in_or_app. right. apply/inP. by rewrite mem_seq1.
      remove_bools_options.
      by apply bet_br => //.
    + (* Weakening *)
      apply bet_weakening.
      by eapply IHHType => //=.
Qed.

Lemma t_Local_tee_num_preserve: forall C v i tf,
    be_typing C [::BI_const_num v; BI_local_tee i] tf ->
    be_typing C [::BI_const_num v; BI_const_num v; BI_local_set i] tf.
Proof.
  move => C v i tf HType.
  dependent induction HType => //.
  - (* Composition *)
    invert_be_typing.
    replace ([::BI_const_num v; BI_const_num v; BI_local_set i]) with ([::BI_const_num v] ++ [::BI_const_num v] ++ [::BI_local_set i]) => //.
    repeat (try rewrite catA; eapply bet_composition) => //.
    + instantiate (1 := (ts ++ [::T_num (typeof_num v)])).
      apply bet_weakening_empty_1. by apply bet_const_num.
    + instantiate (1 := (ts ++ [::T_num (typeof_num v)] ++ [::T_num (typeof_num v)])).
      apply bet_weakening. apply bet_weakening_empty_1. by apply bet_const_num.
    + apply bet_weakening. apply bet_weakening_empty_2. by apply bet_local_set.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType => //=.
Qed.
Lemma t_Local_tee_vec_preserve: forall C v i tf,
    be_typing C [::BI_const_vec v; BI_local_tee i] tf ->
    be_typing C [::BI_const_vec v; BI_const_vec v; BI_local_set i] tf.
Proof.
  move => C v i tf HType.
  dependent induction HType => //.
  - (* Composition *)
    invert_be_typing.
    replace ([::BI_const_vec v; BI_const_vec v; BI_local_set i]) with ([::BI_const_vec v] ++ [::BI_const_vec v] ++ [::BI_local_set i]) => //.
    repeat (try rewrite catA; eapply bet_composition) => //.
    + instantiate (1 := (ts ++ [::T_vec (typeof_vec v)])).
      apply bet_weakening_empty_1. by apply bet_const_vec.
    + instantiate (1 := (ts ++ [::T_vec (typeof_vec v)] ++ [::T_vec (typeof_vec v)])).
      apply bet_weakening. apply bet_weakening_empty_1. by apply bet_const_vec.
    + apply bet_weakening. apply bet_weakening_empty_2. by apply bet_local_set.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType => //=.
Qed.
Lemma t_Local_tee_null_preserve: forall C v i tf,
    be_typing C [::BI_ref_null v; BI_local_tee i] tf ->
    be_typing C [::BI_ref_null v; BI_ref_null v; BI_local_set i] tf.
Proof.
  move => C v i tf HType.
  dependent induction HType => //.
  - (* Composition *)
    invert_be_typing; simpl in *.
    replace ([::BI_ref_null v; BI_ref_null v; BI_local_set i]) with ([::BI_ref_null v] ++ [::BI_ref_null v] ++ [::BI_local_set i]) => //.
    repeat (try rewrite catA; eapply bet_composition) => //.
    + instantiate (1 := (ts ++ [::T_ref v])).
      apply bet_weakening_empty_1. by apply bet_ref_null.
    + instantiate (1 := (ts ++ [::T_ref v] ++ [::T_ref v])).
      apply bet_weakening. apply bet_weakening_empty_1. by apply bet_ref_null.
    + apply bet_weakening. apply bet_weakening_empty_2.
      apply bet_local_set => //=.
  - (* Weakening *)
    apply bet_weakening.
    by eapply IHHType => //=.
Qed.

(*
  Preservation for all be_typeable simple reductions.
*)

Theorem t_be_simple_preservation: forall bes bes' es es' C tf,
    be_typing C bes tf ->
    reduce_simple es es' ->
    es_is_basic es ->
    es_is_basic es' ->
    to_e_list bes = es ->
    to_e_list bes' = es' ->
    be_typing C bes' tf.
Proof.
  move => bes bes' es es' C tf HType HReduce HAI_basic1 HAI_basic2 HBES1 HBES2.
  destruct tf.
  inversion HReduce; b_to_a_revert; subst; simpl in HType => //; basic_inversion.
(* The proof itself should be refactorable further into tactics as well. *)
  - (* Unop *)
    by eapply t_Unop_num_preserve; eauto => //=.
  - (* Binop_success *)
    by eapply t_Binop_preserve_success; eauto => //=.
  - (* testop_i T_i32 *)
    by apply t_Testop_i32_preserve => //.
  - (* testop_i T_i64 *)
    by apply t_Testop_i64_preserve => //.
  - (* relop *)
    by eapply t_Relop_preserve => //=; eauto.
  - (* Cvtop Convert success *)
    eapply t_Convert_preserve => //=.
    apply HType.
    by apply rs_convert_success => //=.
  - (* Cvtop Reinterpret *)
    eapply t_Reinterpret_preserve => //=.
    apply HType.
    by apply rs_reinterpret => //=.
  - (* rs_ref_is_null_true: *)
    eapply t_Ref_is_null_true_preserve_be with (ref := t) => //=.
  - (* rs_ref_is_null_false: *)
    exfalso. remember (Tf r r0) as tf.
    eapply t_Ref_is_null_false_preserve_be with C ref tf => //=.
  - (* Nop *)
    apply Nop_typing in HType; subst;
    apply bet_weakening_empty_both;
    by apply bet_empty.
  - (* Drop *)
    eapply t_Drop_preserve => //=;
    by apply HType.
  - (* Select_false *)
    unfold es_is_basic, e_is_basic in H3.
    apply List.Forall_inv in H3. destruct H3.
    replace ([:: v_to_e v2]) with ([:: AI_basic x]) in HReduce;
      last by rewrite H.
    simpl. replace (to_b_single (v_to_e v2)) with (x) => //=;
      last by rewrite H.
    destruct ot => //=.
    + induction l => //=.
      * exfalso. eapply t_Select_some_preserve_nil with 
          (v1 := v1) (v2 := v2) (n := Wasm_int.int_zero i32m)
          (tf := (Tf r r0)) (C := C) (be := x) => //=.
      * eapply t_Select_some_preserve with (n := Wasm_int.int_zero i32m)
          (v1 := v1) (v2 := v2) (t := a) (ts := l) => //=.
    + eapply t_Select_none_preserve with (n := Wasm_int.int_zero i32m)
          (v1 := v1) (v2 := v2) => //=.
  - (* Select_true *)
    unfold es_is_basic, e_is_basic in H3.
    apply List.Forall_inv in H3. destruct H3.
    replace ([:: v_to_e v1]) with ([:: AI_basic x]) in HReduce;
      last by rewrite H0.
    simpl. replace (to_b_single (v_to_e v1)) with (x) => //=;
      last by rewrite H0.
    destruct ot => //=.
    + induction l => //=.
    * exfalso. eapply t_Select_some_preserve_nil with 
        (v1 := v1) (v2 := v2) (n := n)
        (tf := (Tf r r0)) (C := C) (be := x) => //=.
    * eapply t_Select_some_preserve with (n := n)
        (v1 := v1) (v2 := v2) (t := a) (ts := l) => //=.
    + eapply t_Select_none_preserve with (n := n)
          (v1 := v1) (v2 := v2) => //=.
  - (* br_if_0 *)
    eapply t_Br_if_false_preserve => //=.
    + by apply HType.
    + by apply rs_br_if_false.
  - (* br_if_n0 *)
    eapply t_Br_if_true_preserve => //=.
    + by apply HType.
    + by apply rs_br_if_true.
  - (* br_table -- in range *)
    eapply t_Br_table_preserve => //=.
    + by apply HType.
    + by apply rs_br_table.
  - (* br_table -- out of range default *)
    eapply t_Br_table_preserve => //=.
    + by apply HType.
    + by apply rs_br_table_length.
  - (* tee_local *)
    unfold is_const in H.
    destruct v => //;
    [ destruct b => // | destruct f => // | destruct e => //];
    unfold to_b_single in *; simpl in *;
    try (
      unfold es_is_basic in HAI_basic1;
      apply List.Forall_inv in HAI_basic1;
      destruct HAI_basic1; discriminate
    ).
    + by apply t_Local_tee_null_preserve.
    + by apply t_Local_tee_num_preserve.
    + by apply t_Local_tee_vec_preserve.
Qed.

Ltac auto_basic :=
  repeat lazymatch goal with
  | |- es_is_basic [::AI_basic _; AI_basic _; AI_basic _; AI_basic _] =>
    apply List.Forall_cons => //; repeat split
  | |- es_is_basic [::AI_basic _; AI_basic _; AI_basic _] =>
    apply List.Forall_cons => //; repeat split
  | |- es_is_basic [::AI_basic _; AI_basic _] =>
    apply List.Forall_cons => //; repeat split
  | |- es_is_basic [::AI_basic _] =>
    apply List.Forall_cons => //; repeat split
  | |- List.Forall e_is_basic ?es =>
    fold (es_is_basic es)
  | |- operations.es_is_basic [::AI_basic _; AI_basic _; AI_basic _; AI_basic _] =>
    apply List.Forall_cons => //; repeat split
  | |- operations.es_is_basic [::AI_basic _; AI_basic _; AI_basic _] =>
    apply List.Forall_cons => //; repeat split
  | |- operations.es_is_basic [::AI_basic _; AI_basic _] =>
    apply List.Forall_cons => //; repeat split
  | |- operations.es_is_basic [::AI_basic _] =>
    apply List.Forall_cons => //; repeat split
  | |- List.Forall operations.e_is_basic ?es =>
    fold (es_is_basic es)
  | |- operations.e_is_basic (AI_basic ?e) =>
    by unfold e_is_basic; exists e
end.

(* We need this version for dealing with the version of predicate with host. *)
Ltac basic_inversion'_step :=
  lazymatch goal with
    | H: True |- _ =>
      clear H
    | H: es_is_basic (_ ++ _) |- _ =>
      let Ha := fresh H in
      let Hb := fresh H in
      apply basic_concat in H; destruct H as [Ha Hb]
    | H: es_is_basic [::] |- _ =>
      clear H
    | H: es_is_basic [::_] |- _ =>
      try by (unfold es_is_basic in H; apply List.Forall_inv in H; by inversion H)
    | H: e_is_basic _ |- _ =>
      inversion H; try by []
    end.
Ltac basic_inversion' :=
  repeat basic_inversion'_step.

Lemma t_const_ignores_context: forall s C C' es tf,
    const_list es ->
    e_typing s C es tf ->
    e_typing s C' es tf.
Proof.
  move => s C C' es tf HConst HType.

  (* A trick on doing induction from tail since composition needs that... *)
  remember (rev es) as es'.
  assert (es = rev es'). rewrite Heqes'. symmetry. by apply revK.
  rewrite H.
  generalize dependent tf. generalize dependent es.

  induction es' => //=; move => es HConst HRev1 HRev2 tf HType; destruct tf.
  - subst. simpl in HType.
    unfold rev in HType. simpl in HType. unfold rev. simpl.
    apply ety_a' => //=.
    apply e_empty_typing in HType. subst.
    apply bet_weakening_empty_both. by apply bet_empty.
  - subst.
    simpl. rewrite rev_cons. rewrite -cats1.
    rewrite rev_cons in HType. rewrite -cats1 in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts [t1s' [t2s' [t3s H]]]].
    destruct H as [H1 [H2 [H3 H4]]].
    subst.
    apply ety_weakening.
    rewrite rev_cons in HConst. rewrite -cats1 in HConst.
    apply const_list_split in HConst. destruct HConst.
    eapply ety_composition.
    + eapply IHes' => //.
      -- by apply H.
      -- by rewrite revK.
      -- by apply H3.
    + (* The main reason that this holds *)
      simpl in H0. move/andP in H0. destruct H0.
      destruct a => //=.
      * destruct b => //=;
        try (
          apply et_to_bet in H4;
          last (
            unfold es_is_basic; apply List.Forall_cons => //;
            econstructor; eauto
          );
          unfold to_b_list, map, to_b_single in H4
        );
        [ apply BI_ref_null_typing in H4
        | apply BI_const_num_typing in H4
        | apply BI_const_vec_typing in H4];
        subst; apply et_weakening_empty_1;
        apply ety_a' => //=;
        try (
          unfold es_is_basic; apply List.Forall_cons;
          unfold e_is_basic; eauto
        );
        constructor.
      * apply AI_ref_func_typing in H4.
        destruct H4 as [ft [H4f H4]].
        subst. apply et_weakening_empty_1. eapply ety_ref; eauto.
      * apply AI_ref_extern_typing in H4.
        subst. apply et_weakening_empty_1. eapply ety_ref_extern.
Qed.

Ltac et_dependent_ind H :=
  let Ht := type of H in
  lazymatch Ht with
  | e_typing ?s ?C ?es (Tf ?t1s ?t2s) =>
    let s2 := fresh "s2" in
    let C2 := fresh "C2" in
    let es2 := fresh "es2" in
    let tf2 := fresh "tf2" in
    remember s as s2 eqn:Hrems;
    remember C as C2 eqn:HremC;
    remember es as es2 eqn:Hremes;
    remember (Tf t1s t2s) as tf2 eqn:Hremtf;
    generalize dependent Hrems;
    generalize dependent HremC;
    generalize dependent Hremtf;
    generalize dependent s; generalize dependent C;
    generalize dependent t1s; generalize dependent t2s;
    induction H
  | e_typing ?s ?C ?es ?tf =>
    let s2 := fresh "s2" in
    let C2 := fresh "C2" in
    let es2 := fresh "es2" in
    remember s as s2 eqn:Hrems;
    remember C as C2 eqn:HremC;
    remember es as es2 eqn:Hremes;
    generalize dependent Hrems;
    generalize dependent HremC;
    generalize dependent s; generalize dependent C;
    induction H
  | _ => fail "hypothesis not an e_typing relation"
  end; intros; subst.

Lemma Label_typing: forall s C n es0 es ts1 ts2,
    e_typing s C [::AI_label n es0 es] (Tf ts1 ts2) ->
    exists ts ts2', ts2 = ts1 ++ ts2' /\
                    e_typing s C es0 (Tf ts ts2') /\
                    e_typing s (upd_label C ([::ts] ++ (tc_label C))) es (Tf [::] ts2') /\
                    length ts = n.
Proof.
  move => s C n es0 es ts1 ts2 HType.
(*  (* Without the powerful generalize_dependent tactic, we need to manually remember
     the dependent terms. However, it's very easy to mess up the induction hypothesis
     if variables are not correctly generalized.
     Reading source: https://stackoverflow.com/questions/58349365/coq-how-to-correctly-remember-dependent-values-without-messing-up-the-inductio 
     ( the missing letter n at the end of link is not a typo )
   *)
  remember ([::Label n es0 es]) as les.
  remember (Tf ts1 ts2) as tf.
  generalize dependent Heqtf. generalize dependent ts1. generalize dependent ts2.*)
  et_dependent_ind HType => //.
(*  induction HType => //. *)
  - (* ety_a *)
    assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
    rewrite Hremes in H0. basic_inversion'.
  - (* ety_composition *)
    apply extract_list1 in Hremes. destruct Hremes. subst.
    apply et_to_bet in HType1 => //.
    simpl in HType1. apply empty_typing in HType1. subst.
    by eapply IHHType2 => //.
  - (* ety_weakening *)
    edestruct IHHType => //.
    inversion Hremtf; subst.
    destruct H as [ts2' [H1 [H2 [H3 H4]]]]. subst.
    by exists x, ts2'; try rewrite catA.     
  - (* ety_label *)
    inversion Hremes. inversion Hremtf. subst.
    by exists ts, ts2.
Qed.


(* source: https://staff.math.su.se/anders.mortberg/thesis/doc/refinements/binnat.html *)
Lemma to_natE : forall (p : positive),
  Pos.to_nat p = nat_of_pos p.
Proof.
  by elim => //= p <-;
  rewrite ?Pos2Nat.inj_xI ?Pos2Nat.inj_xO NatTrec.trecE -mul2n.
Qed.

Lemma nat_of_bin_is_N_to_nat: forall x,
  N.to_nat x = nat_of_bin x.
Proof.
  unfold N.to_nat, nat_of_bin.
  induction x => //=. apply to_natE.
Qed.


(*
  Looking at what we want to prove in the Lfilled_break case, it might be tempting to
    prove the following:

Lemma Lfilled_break_typing: forall n lh vs LI ts s C t2s,
    e_typing s (upd_label C ([::ts] ++ tc_label C)) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfilled n lh (vs ++ [::AI_basic (Br n)]) LI ->
    e_typing s C vs (Tf [::] ts).

  The lemma itself is definitely correct, and an apparent approach is to do induction
    on n (or induction on the lfilled hypothesis).

  However, this will *NOT* work: the culprit is that there is no inductive relationship
    that changes the instruction (Br n+1) into (Br n), and we will get a useless
    induction hypothesis that can never be applied.

  We need to somehow avoid getting the parameter of Br into induction. By the lfilled
    hypothesis, we know LI is a nested Label which, at the innermost level, has (Br n)
    as its first non-constant instruction, and vs at the top of the value stack.

  Recall that (Br n) looks at the nth entry in the label of the typing context and
    needs to consume that type. Since we can only induct on the depth of lfilled
    (but not the n in the instruction), they have to be two separate numbers, say
    n and m. Now if n is 0, the instruction will basically look at the mth entry;
    what if n is not 0? In that case if we trace the expansion of LI and simulate
    how the typing is evaluated, we realize that there will be n entries prepended
    to the label of the typing context, after which we'll then find the mth element
    of it due to the (Br m).

  So a more sensible lemma to prove is the following, which the original lemma we
    wanted is a special case of:
*)

Lemma Lfilled_break_typing: forall n m k lh vs LI ts s C t2s tss,
    e_typing s (upd_label C (tss ++ [::ts] ++ tc_label C)) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    @lfilled n lh (vs ++ [::AI_basic (BI_br m)]) LI ->
    length tss = k ->
    bin_of_nat (n + k) = m ->
    e_typing s C vs (Tf [::] ts).
Proof.
  dependent induction n; move => m k; dependent destruction lh;
  move => vs LI ts s C ts2 tss HType HConst Hts HLF Htss HSum;
  unfold lfilled in HLF; simpl in HLF;
  move/eqP in HLF; rewrite <- HLF in HType. (* unfold lfill. *)
  - rewrite add0n in HSum. rewrite -Htss in HSum.
    repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]].
    destruct ts0, t1s => //=. clear H1 H2.
    apply e_composition_typing in H3.
    destruct H3 as [ts0' [t1s' [t2s' [t3s' [H5 [H6 [H7 H8]]]]]]].
    subst t3s. destruct ts0', t1s' => //=. clear H5.
    apply e_composition_typing in H7.
    destruct H7 as [ts0'' [t1s'' [t2s'' [t3s'' [H9 [H10 [H11 H12]]]]]]].
    subst t3s'. destruct ts0'', t1s'' => //=. clear H9.
    apply et_to_bet in H8; try auto_basic.
    apply Break_typing in H8.
    destruct H8 as [ts0 [ts1 [H13 [H14 H15]]]]. clear H13.
    apply const_list_typing in H11; last by apply v_to_e_is_const_list.
    destruct H11 as [H11f H11]. simpl in H11. subst t3s''.
    apply const_list_get in HConst. destruct HConst. subst vs.
    apply const_list_typing in H12; last by apply v_to_e_is_const_list.
    destruct H12 as [H12f H12].
    simpl in H14. move/eqP in H14.
    rename H14 into H0.
    repeat rewrite length_is_size in HTSSLength.
    rewrite -catA in H0.
    unfold lookup_N in H0. simpl in H0.
    rewrite nat_of_bin_is_N_to_nat in H0.
    replace (nat_of_bin (bin_of_nat (length tss))) with (length tss) in H0;
      last by symmetry; apply bin_of_natK.
    rewrite -(cat1s ts _) -HSum in H0. move/eqP in H0.
    replace (nat_of_bin (bin_of_nat (length tss))) with (length tss) in H0;
      last by symmetry; apply bin_of_natK.
    rewrite list_nth_prefix in H0.
    inversion H0. subst. clear H0. rewrite cat0s in H15.
    apply concat_cancel_last_n in H15 => //=;
      last by repeat rewrite length_is_size in Hts;
      rewrite v_to_e_size in Hts; rewrite size_map => //=.
    remove_bools_options. subst.
    apply const_list_typing' => //=; apply v_to_e_is_const_list.

  - unfold lfilled in IHn. rewrite -Htss in HSum. subst.
    apply e_composition_typing_const_list in HType;
    destruct HType as [t3s [H1 HType]]; subst.
    apply const_list_typing in H1; last by apply v_to_e_is_const_list.
    destruct H1 as [H1f H1]. subst.
    rewrite cat0s -(cat1s _ l1) in HType.
    apply e_composition_typing in HType;
    destruct HType as [ts' [t1s [t2s [t3s [H1 [H2 [H3 HType]]]]]]]; subst.
    apply Label_typing in H3.
    destruct H3 as [ts0 [ts2' [Ht3s [Hl0 [Hlh Hts0]]]]]. subst.

    replace ((upd_label (upd_label C (tss ++ [:: ts] ++ tc_label C))
            ([:: ts0] ++ tc_label (upd_label C (tss ++ [:: ts] ++ tc_label C)))))
       with (upd_label C ([:: ts0] ++ tss ++ [:: ts] ++ tc_label C)) in Hlh => //.
    
    remember ([::ts0] ++ tss) as tss'.
    replace (n.+1+length tss) with (n + length tss') in Hlh => //.
    2: {
      assert (length tss' = length tss + 1).
      { rewrite Heqtss'. rewrite cat1s. simpl. by rewrite addn1. }
      by lias.
    }
    
    eapply IHn with (tss := tss') (t2s := ts2') (lh := lh); eauto.
    rewrite (catA [::ts0] tss _) -Heqtss' in Hlh.
    apply Hlh.
Qed.

(*
  And yes, the above observation was obviously the result of some futile attempt
    to prove the unprovable version of the lemma.

Lemma Lfilled_break_typing: forall n lh vs LI ts s C t2s,
    e_typing s (upd_label C ([::ts] ++ tc_label C)) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    lfilled n lh (vs ++ [::AI_basic (Br n)]) LI ->
    e_typing s C vs (Tf [::] ts).
Proof.
  move => n lh vs LI ts s C ts2 HType HConst HLength HLF.
  apply const_es_exists in HConst. destruct HConst. subst.
  move/lfilledP in HLF.
  generalize dependent ts2.
  generalize dependent LI.
  induction n.
  - move => LI HLF ts2 HType.
    repeat rewrite catA in HType.
    inversion HLF.
    apply const_es_exists in H. destruct H. subst.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    subst. clear H1.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H5 [H6 [H7 H8]]]]]]].
    subst.
    apply e_composition_typing in H7.
    destruct H7 as [ts0'' [t1s'' [t2s'' [t3s'' [H9 [H10 [H11 H12]]]]]]].
    subst.
    apply et_to_bet in H12; last by auto_basic.
    apply Break_typing in H12.
    destruct H12 as [ts0 [ts1 [H13 [H14 H15]]]]. clear H13.
    unfold plop2 in H14. simpl in H14. move/eqP in H14. inversion H14. subst.
    clear H14.
    apply et_to_bet in H11; last by (apply const_list_is_basic; apply v_to_e_is_const_list).
    apply Const_list_typing in H11.
    repeat rewrite length_is_size in HLength.
    assert ((ts1 == t1s'') && (ts0 == vs_to_vts x)).
    + apply concat_cancel_last_n => //=. rewrite size_map.
      by rewrite v_to_e_size in HLength.
    + move/andP in H. destruct H.
      move/eqP in H0. subst.
      apply ety_a'; first by apply const_list_is_basic; apply v_to_e_is_const_list.
      by apply Const_list_typing_empty.
  - move => LI HLF ts2 HType.
    inversion HLF. subst.
    repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s [t2s [t3s [H2 [H3 [H4 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s => //=.
    clear H2. clear H3.
    apply e_composition_typing in H4.
    destruct H4 as [ts0' [t1s' [t2s' [t3s' [H6 [H7 [H8 H9]]]]]]].
    destruct ts0' => //=.
    destruct t1s' => //=.
    clear H6. clear H7.
    apply Label_typing in H9.
    destruct H9 as [ts0'' [t2s'' [H10 [H11 [H12 H13]]]]]. subst.
    simpl in H12.

 *)

Lemma Local_typing: forall s C n f es t1s t2s,
    e_typing s C [::AI_local n f es] (Tf t1s t2s) ->
    exists ts, t2s = t1s ++ ts /\
               s_typing s (Some ts) f es ts /\
               length ts = n.
Proof.
  move => s C n f es t1s t2s HType.
  remember ([::AI_local n f es]) as les.
  remember (Tf t1s t2s) as tf.
  generalize dependent Heqtf. generalize dependent t1s. generalize dependent t2s.
  induction HType; subst => //.
  - (* ety_a *)
    assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
    rewrite Heqles in H0. by basic_inversion'.
  - (* ety_composition *)
    apply extract_list1 in Heqles. destruct Heqles. subst.
    apply et_to_bet in HType1 => //.
    simpl in HType1. apply empty_typing in HType1. subst.
    by eapply IHHType2 => //.
  - (* ety_weakening *)
    move => ts2 ts1 HTf.
    inversion HTf. subst.
    edestruct IHHType => //=.
    destruct H as [H1 [H2 H3]]. subst. 
    exists x.
    repeat split => //=.
    by rewrite catA.
  - (* ety_local *)
    inversion Heqles. subst.
    move => t2s t1s HTf. inversion HTf. subst.
    by exists t2s.
Qed.

Lemma Lfilled_return_typing: forall n lh vs LI ts s C lab t2s,
    e_typing s (upd_label C lab) LI (Tf [::] t2s) ->
    const_list vs ->
    length ts = length vs ->
    @lfilled n lh (vs ++ [::AI_basic BI_return]) LI ->
    Some ts = tc_return C ->
    e_typing s C vs (Tf [::] ts).
Proof.
  induction n; dependent destruction lh;
  move => vs LI ts s C lab ts2 HType HConst HLength HLF HReturn;
  unfold lfilled in HLF; simpl in HLF;
  move/eqP in HLF; rewrite <- HLF in HType. (* unfold lfill. *)
  - repeat rewrite catA in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H1 [H2 [H3 H4]]]]]]].
    destruct ts0 => //=.
    destruct t1s0 => //=.
    subst. clear H1.
    apply e_composition_typing in H3.
    destruct H3 as [ts1 [t1s1 [t2s1 [t3s1 [H5 [H6 [H7 H8]]]]]]].
    destruct ts1 => //=.
    destruct t1s1 => //=.
    subst. clear H5.
    apply e_composition_typing in H7.
    destruct H7 as [ts2 [t1s2 [t2s2 [t3s2 [H9 [H10 [H11 H12]]]]]]].
    destruct ts2 => //=.
    destruct t1s2 => //=.
    subst. clear H9. simpl in H8. simpl in H4.
    apply et_to_bet in H8; auto_basic. apply Return_typing in H8.
    destruct H8 as [ts1 [ts2 [H13 H14]]]. subst.
    apply const_list_get in HConst. destruct HConst.
    apply const_list_typing in H11; last by apply v_to_e_is_const_list.
    destruct H11 as [H11f H11]. simpl in H11. subst.
    apply const_list_typing in H12; last by apply v_to_e_is_const_list.
    destruct H12 as [H12f H12].
    simpl in H14. rewrite H14 in HReturn. inversion HReturn. subst.
    apply concat_cancel_last_n in H12;
      last by repeat rewrite length_is_size in HLength;
      rewrite size_map; rewrite size_map in HLength.
    move/andP in H12. destruct H12.
    move/eqP in H. move/eqP in H0. subst.
    apply const_list_typing' => //=. apply v_to_e_is_const_list.

  - unfold lfilled in IHn.
    repeat rewrite catA in HType. rewrite -cat1s in HType.
    apply e_composition_typing in HType.
    destruct HType as [ts0 [t1s0 [t2s0 [t3s0 [H2 [H3 [H4 H5]]]]]]].
    destruct ts0 => //=.
    destruct t1s0 => //=.
    subst. clear H2.
    apply const_list_typing in H4; last by apply v_to_e_is_const_list.
    destruct H4 as [H4f H4]. rewrite cat0s in H4. subst.
    apply e_composition_typing in H5.
    destruct H5 as [ts1 [t1s1 [t2s1 [t3s1 [H6 [H7 [H8 H9]]]]]]]. subst.
    apply Label_typing in H8.
    destruct H8 as [ts' [ts2' [H10 [H11 [H12 H13]]]]].
    subst. simpl in H12.
    eapply IHn; eauto.
Qed.

Lemma Local_return_typing: forall s C vs f LI tf n lh,
    e_typing s C [:: AI_local (length vs) f LI] tf ->
    const_list vs ->
    @lfilled n lh (vs ++ [::AI_basic BI_return]) LI ->
    e_typing s C vs tf.
Proof.
  move => s C vs f LI tf n lh HType HConst HLF.
  destruct tf as [t1s t2s].
  apply Local_typing in HType.
  destruct HType as [ts [H1 [H2 H3]]]. subst.
  inversion H2. inversion H. clear H4. subst. clear H2.
  apply et_weakening_empty_1.
  apply const_list_get in HConst. destruct HConst.
  assert (HET: e_typing s (upd_local_label_return C2 (tc_local C2 ++ map typeof f.(f_locs)) (tc_label C2) (Some ts)) vs (Tf [::] ts)).
  {
    eapply Lfilled_return_typing; eauto.
    rewrite H0. apply v_to_e_is_const_list.
  }
  rewrite H0 in HET.
  apply const_list_typing in HET; last by apply v_to_e_is_const_list.
  destruct HET as [HETf HET].
  simpl in HET. subst.
  apply const_list_typing' => //=. apply v_to_e_is_const_list.
Qed.


Theorem t_simple_preservation: forall s i es es' C loc lab ret tf,
    inst_typing s i C ->
    e_typing s (upd_label (upd_local_label_return C loc (tc_label C) ret) lab) es tf ->
    reduce_simple es es' ->
    e_typing s (upd_label (upd_local_label_return C loc (tc_label C) ret) lab) es' tf.
Proof.
  move => s i es es' C loc lab ret tf HInstType HType HReduce.
  inversion HReduce; subst; try (by (
    apply et_to_bet in HType => //; auto_basic;
    apply ety_a' => //; auto_basic;
    eapply t_be_simple_preservation; try by eauto; auto_basic));
    try by apply ety_trap.
  (* Though only a few cases, these cases are expected to be much more difficult. *)
  { (* ref_is_null *)
    by apply t_Ref_is_null_false_preserve in HType.
  }
  { (* select_drop *)
    rewrite -cat1s in HType. destruct tf as [ts1 ts2].
    apply e_composition_typing in HType.
    destruct HType as [ts [t1s' [t2s' [t3s [H1 [H2 [H3 H4]]]]]]].
    apply const_typing in H3; last by apply v_to_e_is_const.
    destruct H3 as [H3f H3].
    apply et_to_bet in H4;
      last by unfold es_is_basic, e_is_basic;
      apply List.Forall_cons; eauto.
    apply Drop_typing in H4. destruct H4. subst.
    apply concat_cancel_last in H. destruct H. subst.
    apply ety_a' => //. apply bet_weakening_empty_both.
    apply bet_empty.
  }
  { (* select_false *)
    rewrite -cat1s in HType. destruct tf as [ts1 ts2].
    apply e_composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]].
    apply const_typing in H3; last by apply v_to_e_is_const.
    destruct H3 as [H3f H3]. subst.
    rewrite -cat1s in H4.
    apply e_composition_typing in H4.
    destruct H4 as [ts' [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]].
    apply const_typing in H3; last by apply v_to_e_is_const.
    destruct H3 as [H3f' H3]. subst.
    rewrite -cat1s in H4.
    apply e_composition_typing in H4.
    destruct H4 as [ts'' [t1s'' [t2s'' [t3s'' [H1' [H2 [H3 H4]]]]]]].
    apply AI_const_num_typing in H3. subst.
    apply et_to_bet in H4;
      last by unfold es_is_basic, e_is_basic;
      apply List.Forall_cons; eauto.
    destruct ot;
    [ apply Select_typing_Some in H4; destruct H4;
      destruct H as [t [H H']]
    | apply Select_typing_None in H4; destruct H4;
      destruct H as [t [H'' [H H']]]
    ]; subst; simpl in H;
    replace ([:: t; t; T_num T_i32]) with ([:: t; t] ++ [:: T_num T_i32]) in H => //;
    rewrite catA in H;
    apply concat_cancel_last in H; destruct H; subst;
    rewrite -(cat1s (t)) catA catA in H1';
    apply concat_cancel_last in H1'; destruct H1'; subst;
    rewrite catA in H1;
    apply concat_cancel_last in H1; destruct H1; subst;
    repeat apply ety_weakening; apply et_weakening_empty_1;
    apply const_typing' => //=; apply v_to_e_is_const.
  }
  { (* select_true *)
    rewrite -cat1s in HType. destruct tf as [ts1 ts2].
    apply e_composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H1 [H2 [H3 H4]]]]]]].
    apply const_typing in H3; last by apply v_to_e_is_const.
    destruct H3 as [H3f H3]. subst.
    rewrite -cat1s in H4.
    apply e_composition_typing in H4.
    destruct H4 as [ts' [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]].
    apply const_typing in H3; last by apply v_to_e_is_const.
    destruct H3 as [H3f' H3]. subst.
    rewrite -cat1s in H4.
    apply e_composition_typing in H4.
    destruct H4 as [ts'' [t1s'' [t2s'' [t3s'' [H1' [H2 [H3 H4]]]]]]].
    apply AI_const_num_typing in H3. subst.
    apply et_to_bet in H4;
      last by unfold es_is_basic, e_is_basic;
      apply List.Forall_cons; eauto.
    rename H into Hn.
    destruct ot;
    [ apply Select_typing_Some in H4; destruct H4;
      destruct H as [t [H H']]
    | apply Select_typing_None in H4; destruct H4;
      destruct H as [t [H'' [H H']]]
    ]; subst; simpl in H;
    replace ([:: t; t; T_num T_i32]) with ([:: t; t] ++ [:: T_num T_i32]) in H => //;
    rewrite catA in H;
    apply concat_cancel_last in H; destruct H; subst;
    rewrite -(cat1s (t)) catA catA in H1';
    apply concat_cancel_last in H1'; destruct H1'; subst;
    rewrite catA in H1;
    apply concat_cancel_last in H1; destruct H1; subst; rewrite -H1;
    repeat apply ety_weakening; apply et_weakening_empty_1;
    [| rewrite -H1 in H''];
    apply const_typing' => //=; apply v_to_e_is_const.
  }
  - (* Label_const *)
    destruct tf as [ts1 ts2]. apply Label_typing in HType.
    destruct HType as [ts [ts2' [H1 [H2 [H3 H4]]]]]. simpl in *.
    subst. apply et_weakening_empty_1.
    rewrite upd_label_overwrite in H3 => //=.
    eapply t_const_ignores_context; eauto.

 (*   Check HType.
    dependent induction HType.
    Print e_typing.
    gen_ind_pre HType.
    Set Ltac Debug.
    Check Datatypes.cons.
    gen_ind_gen HType.
    gen_ind_subst HType.*)
 (* After several futile attempts to fix gen_ind_gen, I gave up on it and 
      made a more cumbersome et_dependent_ind that only works for e_typing.

    For future reference: the reason gen_ind_gen fails here is because when we get to
      the second last term 
          [::Label n es0 es'] 
      which is effectively
          cons (Label n es0 es') nil
      we first try to generalize the token 'cons', which obviously cannot be 
        generalized (which is fine); but then when we try to look at the term 'Label',
        the tactic somehow wants to generalize on the type of it, i.e.
          'administrative_instruction', 
        which is unfortunately redefined with host to be 
          'administrative_instruction host_function'
        which means we will generalize host_function which is what we tried to avoid.
 *)

  - (* Label_lfilled_Break *)
    et_dependent_ind HType => //.
    + (* ety_a *)
      assert (es_is_basic (operations.to_e_list bes)); first by apply to_e_list_basic.
      rewrite Hremes in H2. by basic_inversion'.
    + (* ety_composition *)
      apply extract_list1 in Hremes. destruct Hremes. subst.
      apply et_to_bet in HType1 => //.
      simpl in HType1. apply empty_typing in HType1. subst.
      by eapply IHHType2 => //=.
    + (* ety_weakening *)
      apply ety_weakening.
      by eapply IHHType => //.
    + (* ety_label *)
      inversion Hremes; subst.
      remember (nat_of_bin i0) as x. assert (i0 = bin_of_nat x) as Hx => //=.
        rewrite Heqx. symmetry. apply nat_of_binK.
      rewrite Hx in H1.
      eapply et_composition' with (t2s := ts) => //=.
      eapply Lfilled_break_typing
        with (tss := [::]) (t2s := t2s) (LI := LI) => //=.
        * simpl. rewrite addn0. by apply H1.
  - (* Local_const *)

    destruct tf as [ts1 ts2]. apply Local_typing in HType.
    destruct HType as [ts [H1 [H2 H3]]]. subst.
    apply et_weakening_empty_1.
    inversion H2. subst.
    apply const_list_get in H. destruct H. rewrite H in H4.
    apply const_list_typing in H4; last by apply v_to_e_is_const_list.
    destruct H4 as [H4f H4]. simpl in H4. subst.
    induction x => //=; first by apply ety_a' => //; apply bet_empty.
    rewrite -cat1s -(cat1s (typeof a)).
    eapply et_composition' with (t2s := [:: typeof a]).
    + apply const_typing' => //=; first by apply v_to_e_is_const.
      apply H4f. rewrite in_cons. apply/orP. by left.
    + apply et_weakening_empty_1.
      apply const_list_typing' => //=; first by apply v_to_e_is_const_list.
      intros v Hv. apply H4f. rewrite in_cons. apply/orP. by right.
      
  - (* Local_lfilled_Return *)
    by eapply Local_return_typing; eauto.

  - (* Tee_local -- actually a simple reduction *)
    destruct v => //.
    + destruct b => //;
      apply et_to_bet in HType => //; auto_basic;
      apply ety_a' => //; auto_basic;
      by eapply t_be_simple_preservation; try by eauto; auto_basic.
    + destruct tf.
      rewrite -cat1s in HType.
      apply e_composition_typing in HType.
      destruct HType as [ts [t1s' [t2s' [t3s [Hr [Hr0 [Hf HType]]]]]]].
      apply AI_ref_func_typing in Hf. destruct Hf as [ft [Hff Hf]]. subst.

      apply ety_weakening.
      rewrite -cat1s.
      eapply et_composition' with (t2s := t1s' ++ [:: T_ref T_funcref]);
        first by apply et_weakening_empty_1; eapply ety_ref; eauto.
      rewrite -cat1s.
      eapply et_composition' with (t2s := (t1s' ++ [:: T_ref T_funcref]) ++ [:: T_ref T_funcref]);
        first by apply et_weakening_empty_1; eapply ety_ref; eauto.
      apply ety_a' => //; auto_basic.

      apply et_to_bet in HType => //; auto_basic.
      apply Local_tee_typing in HType.
      destruct HType as [ts' [t [Ht2s' [Hts' Ht]]]].
      simpl in Ht. subst. apply concat_cancel_last in Hts'.
      destruct Hts'. subst.
      apply bet_weakening_empty_2. eapply bet_local_set; eauto.

    + destruct tf.
      rewrite -cat1s in HType.
      apply e_composition_typing in HType.
      destruct HType as [ts [t1s' [t2s' [t3s [Hr [Hr0 [Hf HType]]]]]]].
      apply AI_ref_extern_typing in Hf. subst.

      apply ety_weakening.
      rewrite -cat1s.
      eapply et_composition' with (t2s := t1s' ++ [:: T_ref T_externref]);
        first by apply et_weakening_empty_1; eapply ety_ref_extern; eauto.
      rewrite -cat1s.
      eapply et_composition' with (t2s := (t1s' ++ [:: T_ref T_externref]) ++ [:: T_ref T_externref]);
        first by apply et_weakening_empty_1; eapply ety_ref_extern; eauto.
      apply ety_a' => //; auto_basic.

      apply et_to_bet in HType => //; auto_basic.
      apply Local_tee_typing in HType.
      destruct HType as [ts' [t [Ht2s' [Hts' Ht]]]].
      simpl in Ht. subst. apply concat_cancel_last in Hts'.
      destruct Hts'. subst.
      apply bet_weakening_empty_2. eapply bet_local_set; eauto.
Qed.

Lemma globs_agree_function: forall s,
    function (globali_agree (s_globals s)).
Proof.
  move => s. unfold function. move => x y1 y2 [H1 H2].
  unfold globali_agree, option_map, global_typing in H1, H2.
  remove_bools_options => //=.
Qed.

Lemma functions_agree_function: forall s,
    function (@funci_agree host_function (s_funcs s)).
Proof.
  move => s. unfold function. move => x y1 y2 [H1 H2].
  unfold funci_agree in H1, H2.
  by remove_bools_options.
Qed.

Lemma tc_func_reference1: forall j k i s f C tf,
  lookup_N (inst_funcs i) j = Some k ->
  lookup_N (s_funcs s) k = Some f ->
  inst_typing s i C ->
  lookup_N (tc_func C) j = Some tf ->
  tf = cl_type f.
Proof.
  move => j k i s f C tf HN1 HN2 HInstType HN3.
  destruct i, C, tc_local, tc_label, tc_return, tc_ref => //=.
  move/andP in HInstType. destruct HInstType.
  repeat (move/andP in H; destruct H).
  simpl in HN1. simpl in HN3.
  eapply all2_projection in H5; eauto.
  unfold funci_agree in H5. rewrite HN2 in H5.
  simpl in H5. move/eqP in H5.
  by inversion H5.
Qed.

Lemma tc_func_reference2: forall s C i j cl tf,
  lookup_N (inst_types i) j = Some (cl_type cl) ->
  inst_typing s i C ->
  lookup_N (tc_type C) j = Some tf ->
  tf = cl_type cl.
Proof.
  move => s C i j cl tf HN1 HIT HN2.
  unfold inst_typing in HIT.
  destruct i, C, tc_local, tc_label, tc_return, tc_ref => //=.
  move/andP in HIT. destruct HIT.
  repeat (move/andP in H; destruct H).
  simpl in HN1. simpl in HN2.
  move/eqP in H. subst.
  rewrite HN1 in HN2.
  by inversion HN2.
Qed.

Lemma Invoke_func_native_typing: forall s i C a cl tn tm ts es t1s t2s,
    e_typing s C [::AI_invoke a] (Tf t1s t2s) ->
    lookup_N (s_funcs s) a = Some cl ->
    cl = FC_func_native i (Tf tn tm) ts es ->
    exists ts' C', t1s = ts' ++ tn /\ t2s = ts' ++ tm /\
                inst_typing s i C' /\
                be_typing (upd_local_label_return C' (tc_local C' ++ tn ++ ts) ([::tm] ++ tc_label C') (Some tm)) es (Tf [::] tm).
Proof.
  move => s i C a cl tn tm ts es t1s t2s HType HNth Hcl.
  et_dependent_ind HType => //.
  - by destruct bes => //=.
  - apply extract_list1 in Hremes. destruct Hremes. subst.
    apply et_to_bet in HType1 => //=.
    apply empty_typing in HType1. subst.
    by eapply IHHType2 => //=.
  - inversion Hremtf; subst.
    edestruct IHHType => //=.
    destruct H as [C' [H1 [H2 [H3 H4]]]]. subst.
    exists (ts0 ++ x), C'.
    by repeat split => //; rewrite catA.
  - inversion Hremes; subst.
    rewrite H in HNth.
    inversion HNth; subst; clear HNth.
    inversion H0; subst.
    inversion H9; subst.
    by exists [::], C.
Qed.

Lemma Invoke_func_host_typing: forall s C a cl h tn tm t1s t2s,
    e_typing s C [::AI_invoke a] (Tf t1s t2s) ->
    lookup_N (s_funcs s) a = Some cl ->
    cl = FC_func_host (Tf tn tm) h ->
    exists ts, t1s = ts ++ tn /\ t2s = ts ++ tm.
Proof.
  move => s C a cl h tn tm t1s t2s HType HNth Hcl.
  et_dependent_ind HType => //.
  - by destruct bes => //=.
  - apply extract_list1 in Hremes. destruct Hremes. subst.
    apply et_to_bet in HType1 => //=.
    apply empty_typing in HType1. subst.
    by eapply IHHType2 => //=.
  - inversion Hremtf; subst.
    edestruct IHHType => //=.
    exists (ts ++ x). destruct H. subst.
    by split; repeat rewrite catA.
  - inversion Hremes; subst.
    rewrite H in HNth.
    inversion HNth; subst; clear HNth.
    inversion H0; subst.
    by exists [::].
Qed.

Lemma store_typed_cl_typed: forall s n f,
    lookup_N (s_funcs s) n = Some f ->
    store_typing s ->
    cl_typing s f (cl_type f).
Proof.
  move => s n f HN HST.
  unfold store_typing in HST.
  destruct s => //=.
  remove_bools_options.
  simpl in HN.
  destruct HST.
  (* arrow actually required to avoid ssreflect hijacking the rewrite tactic! *)
  rewrite -> List.Forall_forall in H.
  apply List.nth_error_In in HN.
  apply H in HN. unfold cl_type_check_single in HN. destruct HN.
  by inversion H1; subst.
Qed.

Lemma inst_t_context_local_empty: forall s i C,
    inst_typing s i C ->
    tc_local C = [::].
Proof.
  move => s i C HInstType.
  destruct i, C, tc_local => //=.
Qed.

Lemma inst_t_context_label_empty: forall s i C,
    inst_typing s i C ->
    tc_label C = [::].
Proof.
  move => s i C HInstType.
  destruct i, C, tc_local, tc_label => //=.
Qed.


Lemma inst_index_get_contextval_mem: forall s i j C a,
  inst_typing s i C ->
  List.nth_error i.(inst_mems) j = Some a ->
  exists x, List.nth_error C.(tc_memory) j = Some x.
Proof.
  move => s i j C a HIT HNth.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.

  rewrite all2E in H2. remove_bools_options.
  assert (List.nth_error inst_mems j <> None) as H';
    first by rewrite HNth.
  apply List.nth_error_Some in H'.
  repeat rewrite -length_is_size in H2.
  rewrite H2 in H'.
  apply List.nth_error_Some in H'.
  destruct (List.nth_error tc_memory j) => //=; eauto.
Qed.
Lemma inst_index_get_instval_mem: forall s i j C x,
  inst_typing s i C ->
  List.nth_error C.(tc_memory) j = Some x ->
  exists a, List.nth_error i.(inst_mems) j = Some a.
Proof.
  move => s i j C x HIT HNth.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.

  rewrite all2E in H2. remove_bools_options.
  assert (List.nth_error tc_memory j <> None) as H';
    first by rewrite HNth.
  apply List.nth_error_Some in H'.
  repeat rewrite -length_is_size in H2.
  rewrite -H2 in H'.
  apply List.nth_error_Some in H'.
  destruct (List.nth_error inst_mems j) => //=; eauto.
Qed.
Lemma inst_typing_mem: forall s i j C a x,
  inst_typing s i C ->
  List.nth_error i.(inst_mems) j = Some a ->
  List.nth_error C.(tc_memory) j = Some x ->
  exists cl, List.nth_error s.(s_mems) (N.to_nat a) = Some cl.
Proof.
  move => s i j C a x HIT HNth1 HNth2.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.
  unfold memi_agree, lookup_N in H2.
  eapply all2_projection in H2; eauto.
  by remove_bools_options; eauto.
Qed.

Lemma inst_index_get_contextval_tab: forall s i j C a,
  inst_typing s i C ->
  List.nth_error i.(inst_tables) j = Some a ->
  exists x, List.nth_error C.(tc_table) j = Some x.
Proof.
  move => s i j C a HIT HNth.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.

  rewrite all2E in H3. remove_bools_options.
  assert (List.nth_error inst_tables j <> None) as H';
    first by rewrite HNth.
  apply List.nth_error_Some in H'.
  repeat rewrite -length_is_size in H3.
  rewrite H3 in H'.
  apply List.nth_error_Some in H'.
  destruct (List.nth_error tc_table j) => //=; eauto.
Qed.
Lemma inst_index_get_instval_tab: forall s i j C x,
  inst_typing s i C ->
  List.nth_error C.(tc_table) j = Some x ->
  exists a, List.nth_error i.(inst_tables) j = Some a.
Proof.
  move => s i j C x HIT HNth.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.

  rewrite all2E in H3. remove_bools_options.
  assert (List.nth_error tc_table j <> None) as H';
    first by rewrite HNth.
  apply List.nth_error_Some in H'.
  repeat rewrite -length_is_size in H3.
  rewrite -H3 in H'.
  apply List.nth_error_Some in H'.
  destruct (List.nth_error inst_tables j) => //=; eauto.
Qed.
Lemma inst_typing_tab: forall s i j C a x,
  inst_typing s i C ->
  List.nth_error i.(inst_tables) j = Some a ->
  List.nth_error C.(tc_table) j = Some x ->
  exists cl, List.nth_error s.(s_tables) (N.to_nat a) = Some cl.
Proof.
  move => s i j C a x HIT HNth1 HNth2.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.
  unfold tabi_agree, lookup_N in H3.
  eapply all2_projection in H3; eauto.
  by remove_bools_options; eauto.
Qed.

Lemma inst_index_get_contextval_global: forall s i j C a,
  inst_typing s i C ->
  List.nth_error i.(inst_globals) j = Some a ->
  exists x, List.nth_error C.(tc_global) j = Some x.
Proof.
  move => s i j C a HIT HNth.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.

  rewrite all2E in H4. remove_bools_options.
  assert (List.nth_error inst_globals j <> None) as H';
    first by rewrite HNth.
  apply List.nth_error_Some in H'.
  repeat rewrite -length_is_size in H4.
  rewrite H4 in H'.
  apply List.nth_error_Some in H'.
  destruct (List.nth_error tc_global j) => //=; eauto.
Qed.
Lemma inst_index_get_instval_global: forall s i j C x,
  inst_typing s i C ->
  List.nth_error C.(tc_global) j = Some x ->
  exists a, List.nth_error i.(inst_globals) j = Some a.
Proof.
  move => s i j C x HIT HNth.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.

  rewrite all2E in H4. remove_bools_options.
  assert (List.nth_error tc_global j <> None) as H';
    first by rewrite HNth.
  apply List.nth_error_Some in H'.
  repeat rewrite -length_is_size in H4.
  rewrite -H4 in H'.
  apply List.nth_error_Some in H'.
  destruct (List.nth_error inst_globals j) => //=; eauto.
Qed.
Lemma inst_typing_global: forall s i j C a x,
  inst_typing s i C ->
  List.nth_error i.(inst_globals) j = Some a ->
  List.nth_error C.(tc_global) j = Some x ->
  exists cl, List.nth_error s.(s_globals) (N.to_nat a) = Some cl.
Proof.
  move => s i j C a x HIT HNth1 HNth2.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.
  unfold globali_agree, lookup_N in H4.
  eapply all2_projection in H4; eauto.
  by remove_bools_options; eauto.
Qed.

Lemma inst_index_get_contextval_func: forall s i j C a,
  inst_typing s i C ->
  List.nth_error i.(inst_funcs) j = Some a ->
  exists x, List.nth_error C.(tc_func) j = Some x.
Proof.
  move => s i j C a HIT HNth.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.

  rewrite all2E in H5. remove_bools_options.
  assert (List.nth_error inst_funcs j <> None) as H';
    first by rewrite HNth.
  apply List.nth_error_Some in H'.
  repeat rewrite -length_is_size in H5.
  rewrite H5 in H'.
  apply List.nth_error_Some in H'.
  destruct (List.nth_error tc_func j) => //=; eauto.
Qed.
Lemma inst_index_get_instval_func: forall s i j C x,
  inst_typing s i C ->
  List.nth_error C.(tc_func) j = Some x ->
  exists a, List.nth_error i.(inst_funcs) j = Some a.
Proof.
  move => s i j C x HIT HNth.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.

  rewrite all2E in H5. remove_bools_options.
  assert (List.nth_error tc_func j <> None) as H';
    first by rewrite HNth.
  apply List.nth_error_Some in H'.
  repeat rewrite -length_is_size in H5.
  rewrite -H5 in H'.
  apply List.nth_error_Some in H'.
  destruct (List.nth_error inst_funcs j) => //=; eauto.
Qed.
Lemma inst_typing_func: forall s i j C a x,
  inst_typing s i C ->
  List.nth_error i.(inst_funcs) j = Some a ->
  List.nth_error C.(tc_func) j = Some x ->
  exists cl, List.nth_error s.(s_funcs) (N.to_nat a) = Some cl.
Proof.
  move => s i j C a x HIT HNth1 HNth2.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.
  unfold funci_agree, lookup_N in H5.
  eapply all2_projection in H5; eauto.
  by remove_bools_options; eauto.
Qed.

Lemma inst_index_get_contextval_elem: forall s i j C a,
  inst_typing s i C ->
  List.nth_error i.(inst_elems) j = Some a ->
  exists x, List.nth_error C.(tc_elem) j = Some x.
Proof.
  move => s i j C a HIT HNth.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.

  rewrite all2E in H1. remove_bools_options.
  assert (List.nth_error inst_elems j <> None) as H';
    first by rewrite HNth.
  apply List.nth_error_Some in H'.
  repeat rewrite -length_is_size in H1.
  rewrite H1 in H'.
  apply List.nth_error_Some in H'.
  destruct (List.nth_error tc_elem j) => //=; eauto.
Qed.
Lemma inst_index_get_instval_elem: forall s i j C x,
  inst_typing s i C ->
  List.nth_error C.(tc_elem) j = Some x ->
  exists a, List.nth_error i.(inst_elems) j = Some a.
Proof.
  move => s i j C x HIT HNth.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.

  rewrite all2E in H1. remove_bools_options.
  assert (List.nth_error tc_elem j <> None) as H';
    first by rewrite HNth.
  apply List.nth_error_Some in H'.
  repeat rewrite -length_is_size in H1.
  rewrite -H1 in H'.
  apply List.nth_error_Some in H'.
  destruct (List.nth_error inst_elems j) => //=; eauto.
Qed.
Lemma inst_typing_elem: forall s i j C a x,
  inst_typing s i C ->
  List.nth_error i.(inst_elems) j = Some a ->
  List.nth_error C.(tc_elem) j = Some x ->
  exists cl, List.nth_error s.(s_elems) (N.to_nat a) = Some cl.
Proof.
  move => s i j C a x HIT HNth1 HNth2.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.
  unfold elemi_agree, lookup_N in H1.
  eapply all2_projection in H1; eauto.
  by remove_bools_options; eauto.
Qed.

Lemma inst_index_get_contextval_data: forall s i j C a,
  inst_typing s i C ->
  List.nth_error i.(inst_datas) j = Some a ->
  exists x, List.nth_error C.(tc_data) j = Some x.
Proof.
  move => s i j C a HIT HNth.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.

  rewrite all2E in H0. remove_bools_options.
  assert (List.nth_error inst_datas j <> None) as H';
    first by rewrite HNth.
  apply List.nth_error_Some in H'.
  repeat rewrite -length_is_size in H0.
  rewrite H0 in H'.
  apply List.nth_error_Some in H'.
  destruct (List.nth_error tc_data j) => //=; eauto.
Qed.
Lemma inst_index_get_instval_data: forall s i j C x,
  inst_typing s i C ->
  List.nth_error C.(tc_data) j = Some x ->
  exists a, List.nth_error i.(inst_datas) j = Some a.
Proof.
  move => s i j C x HIT HNth.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.

  rewrite all2E in H0. remove_bools_options.
  assert (List.nth_error tc_data j <> None) as H';
    first by rewrite HNth.
  apply List.nth_error_Some in H'.
  repeat rewrite -length_is_size in H0.
  rewrite -H0 in H'.
  apply List.nth_error_Some in H'.
  destruct (List.nth_error inst_datas j) => //=; eauto.
Qed.
Lemma inst_typing_data: forall s i j C a x,
  inst_typing s i C ->
  List.nth_error i.(inst_datas) j = Some a ->
  List.nth_error C.(tc_data) j = Some x ->
  exists cl, List.nth_error s.(s_datas) (N.to_nat a) = Some cl.
Proof.
  move => s i j C a x HIT HNth1 HNth2.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.
  unfold datai_agree, lookup_N in H0.
  eapply all2_projection in H0; eauto.
  by remove_bools_options; eauto.
Qed.

Lemma inst_typing_tab_ttype: forall s i x C a ttype tab,
  inst_typing s i C ->
  List.nth_error i.(inst_tables) x = Some a ->
  List.nth_error C.(tc_table) x = Some ttype ->
  List.nth_error s.(s_tables) (N.to_nat a) = Some tab ->
  tableinst_type tab = ttype.
Proof.
  move => s i x C a ttype tab HIT HILU HCLU HSLU.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.

  unfold tabi_agree in H3.
  eapply all2_projection in H3; eauto.
  remove_bools_options; eauto.
  unfold lookup_N in Hoption.
  rewrite Hoption in HSLU. inversion HSLU. subst.
  unfold tab_typing in H7. by remove_bools_options.
Qed.

Lemma inst_typing_elemv_type: forall s i C x j a etype elem elemv,
  inst_typing s i C ->
  List.nth_error i.(inst_elems) x = Some a ->
  List.nth_error C.(tc_elem) x = Some etype ->
  List.nth_error s.(s_elems) (N.to_nat a) = Some elem ->
  List.nth_error (eleminst_elem elem) j = Some elemv ->
  etype = typeof_ref elemv.
Proof.
  move => s i C x j a etype elem elemv HST HILU HCLU HSLU HTLU.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.
  eapply all2_projection in H1; eauto.
  unfold elemi_agree, option_map, lookup_N in H1.
  rewrite HSLU in H1. move/eqP in H1. inversion H1.
  unfold elem_typing in H7.
  remove_bools_options. move/List.forallb_forall in H7.
  symmetry. apply/eqP. apply (H7 elemv).
  eapply List.nth_error_In; eauto.
Qed.

Lemma store_typing_tabv_type: forall s i C x j a tab tabv,
  store_typing s ->
  inst_typing s i C ->
  List.nth_error i.(inst_tables) x = Some a ->
  List.nth_error s.(s_tables) (N.to_nat a) = Some tab ->
  List.nth_error (tableinst_elem tab) (Z.to_nat (Wasm_int.Int32.unsigned j)) = Some tabv ->
  tt_elem_type (tableinst_type tab) = typeof_ref tabv.
Proof.
  move => s i C x j a tab tabv HST HIT HILU HSLU HTLU.
  destruct s, i, C, tc_local, tc_label, tc_return, tc_ref => //=;
  unfold inst_typing, typing.inst_typing in * => //=;
  remove_bools_options; simpl in * => //=.
  destruct HST as [HSTf [HSTt HSTm]].
  move/List.Forall_forall in HSTt.
  destruct (HSTt tab); first by eapply List.nth_error_In; eauto.
  move/List.Forall_forall in H6.
  assert (tabcl_agree
          {|
            s_funcs := s_funcs;
            s_tables := s_tables;
            datatypes.s_mems := s_mems0;
            datatypes.s_globals := s_globals0;
            s_elems := s_elems;
            s_datas := s_datas
          |} (tt_elem_type (tableinst_type tab)) tabv);
  first by apply H6; eapply List.nth_error_In; eauto.
  unfold tabcl_agree in H8.
  destruct tabv => //=.
  destruct H8 => //=.
Qed.

Lemma global_type_reference: forall s i j C v t,
    inst_typing s i C ->
    sglob_val s i j = Some v ->
    option_map tg_t (List.nth_error (tc_global C) j) = Some t ->
    typeof v = t.
Proof.
  move => s i j C v t HInstType Hvref Htref.
  unfold sglob_val in Hvref.
  unfold sglob in Hvref.
  unfold sglob_ind in Hvref.
  destruct (List.nth_error (inst_globals i) j) eqn:Hi => //=.
  remove_bools_options.
  unfold option_bind in Hoption0.
  remove_bools_options.
  unfold inst_typing in HInstType.
  destruct i, C, tc_local, tc_label, tc_return, tc_ref => //=.
  move/andP in HInstType. destruct HInstType.
  remove_bools_options.
  eapply all2_projection in H4; eauto.
  unfold globali_agree, option_map, global_typing in H4.
  by remove_bools_options.
Qed.

(* elem? can't do this then since no elemi_agree?
Lemma table_type_reference: forall s f C x i tabv ttype,
    inst_typing s (f_inst f) C ->
    stab_elem s (f_inst f) x (Wasm_int.N_of_uint i32m i) = Some tabv ->
    lookup_N (tc_table C) x = Some ttype ->
    typeof_ref tabv = tt_elem_type ttype.
Proof.
  move => s f C x i tabv ttype HInstType Href Href'.
  unfold stab_elem, stab in Href.
  destruct (lookup_N (inst_tables (f_inst f)) x) eqn:Hx => //=.
  remove_bools_options.
  unfold inst_typing, typing.inst_typing in HInstType.
  destruct (f_inst f), C, tc_local, tc_label, tc_return, tc_ref => //=.
  move/andP in HInstType. destruct HInstType.
  remove_bools_options.
  eapply all2_projection in H1; eauto.
  unfold tabi_agree in H1.
  remove_bools_options. simpl in Hx.
  unfold tab_typing in H5.
  apply global_val_type_rect.
Qed.
*)

Lemma upd_label_unchanged: forall C lab,
    tc_label C = lab ->
    upd_label C lab = C.
Proof.
  move => C lab HLab.
  rewrite -HLab. unfold upd_label. by destruct C.
Qed.

Lemma upd_label_unchanged_typing: forall s C es tf,
    e_typing s C es tf ->
    e_typing s (upd_label C (tc_label C)) es tf.
Proof.
  move => s C es tf HType.
  by rewrite upd_label_unchanged.
Qed.

(* generalised: old was equivalent to lab' = (tc_label C) *)
Lemma upd_label_upd_local_return_combine: forall C loc lab lab' ret,
    upd_label (upd_local_label_return C loc lab' ret) lab =
    upd_local_label_return C loc lab ret.
Proof.
  by [].
Qed.

Lemma set_nth_same_unchanged: forall {X:Type} (l:seq X) e i vd,
    List.nth_error l i = Some e ->
    set_nth vd l i e = l.
Proof.
  move => X l e i.
  generalize dependent l. generalize dependent e.
  induction i; move => e l vd HNth => //=.
  - destruct l => //=.
    simpl in HNth. by inversion HNth.
  - destruct l => //=.
    f_equal. apply IHi.
    by simpl in HNth.
Qed.

Lemma set_nth_map: forall {X Y:Type} (l:seq X) e i vd {f: X -> Y},
    i < size l ->
    map f (set_nth vd l i e) = set_nth (f vd) (map f l) i (f e).
Proof.
  move => X Y l e i.
  generalize dependent l. generalize dependent e.
  induction i; move => e l vd f HSize => //=.
  - by destruct l => //=.
  - destruct l => //=.
    f_equal.
    apply IHi.
    by simpl in HSize.
Qed.

Lemma n_zeros_typing: forall ts,
    map typeof (n_zeros ts) = ts.
Proof.
  induction ts => //=.
  destruct a; [destruct n | destruct v | destruct r ] => //=;
  f_equal; apply IHts.
Qed.

Lemma funci_agree_extension: forall fs0 fs1 f g,
  size fs0 <= size fs1 ->
  funci_agree fs0 f g ->
  all2 (@func_extension host_function) fs0 (List.firstn (length (fs0)) fs1) ->
  funci_agree fs1 f g.
Proof.
  move => fs0 fs1 f g H0 H1 H2.
  assert (size fs0 = size (List.firstn (length (fs0)) fs1)) as HSize;
    first by eapply all2_size; eauto.
  unfold funci_agree.
  unfold funci_agree in H1. unfold mem_extension in H2.
  destruct g => //=.
  remove_bools_options.
  unfold option_map.
  assert (lookup_N fs0 f <> None) as Hn. rewrite Hoption => //.
  apply lookup_N_Some in Hn.
  rewrite length_is_size in Hn. rewrite HSize in Hn.
  rewrite <- length_is_size in Hn.
  move/ltP in Hn.
  rewrite <- List.nth_error_Some in Hn.
  unfold lookup_N.
  destruct (List.nth_error (List.firstn (length (fs0)) fs1) (N.to_nat f)) eqn:HN => //=.
  (* unfold mem_typing. *)
  eapply all2_projection in H2; [| by apply Hoption | by apply HN ].
  (* unfold mem_typing in H0. simpl in H0. *)
  unfold func_extension in H2. move/eqP in H2. rewrite H2 => //=.
  assert (List.nth_error fs1 (N.to_nat f) = Some f1);
    first by eapply nth_error_firstn; eauto.
  by rewrite H.
Qed.

Lemma func_extension_C: forall sf sf' f tcf,
  size sf <= size sf' ->
  all2 (funci_agree sf) f tcf ->
  all2 (@func_extension host_function) sf (List.firstn (length (sf)) sf') ->
  all2 (funci_agree sf') f tcf.
Proof.
  move => sf sf' f.
  generalize dependent sf; generalize dependent sf'.
  induction f; move => sf' sf tcf HLen HA Hext => //=; destruct tcf => //=.
  simpl in HA. remove_bools_options.
  apply/andP; split => //=; last by eapply IHf; eauto.
  by eapply funci_agree_extension; eauto.
Qed.

Lemma global_agree_extension: forall g0 g1 g,
  g_type g0 == g_type g ->
  global_extension g0 g1 ->
  g_type g1 == g_type g.
Proof.
  move => g0 g1 g H1 H2.
  unfold global_extension in H2.
  destruct g, g0, g1 => //=.
  simpl in H1. simpl in H2.
  destruct g_type => //=.
  remove_bools_options. subst => //=.
Qed.

Lemma global_extension_C: forall sg sg' ig tcg,
  size sg <= size sg' ->
  all2 (globali_agree sg) ig tcg ->
  all2 global_extension sg (List.firstn (length (sg)) sg') ->
  all2 (globali_agree sg') ig tcg.
Proof.
  move => sg sg' ig.
  generalize dependent sg; generalize dependent sg'.
  induction ig; move => sg' sg tcg HLen HA Hext => //=; destruct tcg => //=.
  - simpl in HA. remove_bools_options.
    edestruct IHig; eauto.
    unfold globali_agree in H. remove_bools_options.
    assert (size sg = size (List.firstn (length (sg)) sg'));
      first by eapply all2_size; eauto.
    assert (N.to_nat a < length (List.firstn (length (sg)) sg'))%coq_nat.
    {
      assert (lookup_N sg a <> None) as Hn. rewrite Hoption => //.
      apply lookup_N_Some in Hn.
      rewrite length_is_size in Hn. rewrite length_is_size.
      rewrite -H. rewrite <- length_is_size. by lias.
    }
    remember H1 as H5. clear HeqH5.
    rewrite <- List.nth_error_Some in H1.
    destruct (List.nth_error
        (List.firstn (length (sg)) sg') (N.to_nat a)) eqn:HGlob => //=; eauto.
    clear H1. remember Hext as Hext1. clear HeqHext1.
    eapply all2_projection in Hext1; eauto.
    apply/andP. split => //=.
    + unfold globali_agree, option_map, lookup_N, global_typing.
      assert (List.nth_error sg' (N.to_nat a) = Some g1);
        first by eapply nth_error_firstn; eauto.
      unfold globali_agree, option_map, lookup_N, global_typing in H2.
      move/eqP in H2. remove_bools_options. rewrite H1.
      assert (g_type g1 == g_type g0);
        first by eapply global_agree_extension; eauto.
      subst. rewrite H4. simpl. apply/eqP. f_equal. apply/eqP.
      admit.
      (* back to the same problem: typeof (g_val g0) = tg_t (g_type g0) *)
    + by eapply IHig; eauto.
(* Qed. *) Admitted.

Lemma memi_agree_extension: forall m0 m1 n m,
  size m0 <= size m1 ->
  memi_agree m0 n m ->
  all2 mem_extension m0 (List.firstn (length (m0)) m1) ->
  memi_agree m1 n m.
Proof.
  move => m0 m1 n m HLen H1 H2.
  assert (size m0 = size (List.firstn (length (m0)) m1)) as HSize;
    first by eapply all2_size; eauto.
  unfold memi_agree.
  unfold memi_agree in H1. unfold mem_extension in H2.
  destruct m => //=.
  remove_bools_options.
  unfold option_map.
  assert (lookup_N m0 n <> None) as Hn. rewrite Hoption => //.
  apply lookup_N_Some in Hn.
  rewrite length_is_size in Hn. rewrite HSize in Hn.
  rewrite <- length_is_size in Hn.
  move/ltP in Hn.
  rewrite <- List.nth_error_Some in Hn.
  unfold lookup_N.
  destruct (List.nth_error (List.firstn (length (m0)) m1) (N.to_nat n)) eqn:HN => //=.
  rewrite H0. apply/eqP. f_equal. apply/eqP => //=. 
  eapply all2_projection in H2; [| by apply Hoption | by apply HN ].
  move/andP in H2. destruct H2. move/eqP in H.
  unfold mem_typing in H0. simpl in H0.
  remove_bools_options. unfold mem_typing => //=.
  assert (List.nth_error m1 (N.to_nat n) = Some m2);
    first by eapply nth_error_firstn; eauto.
  rewrite H3. rewrite <- H. rewrite H2.
  apply/eqP => //=. f_equal. apply/andP. split => //=.
  unfold mem_size in *.
  apply N.leb_le. apply N.leb_le in H0, H1.
  assert ((mem_length m / page_size <= mem_length m2 / page_size)%N);
    first by apply N.div_le_mono => //=.
  eapply N.le_trans; eauto.
Qed.

Lemma mem_extension_C: forall sm sm' im tcm,
  size sm <= size sm' ->
  all2 (memi_agree sm) im tcm ->
  all2 mem_extension sm (List.firstn (length (sm)) sm') ->
  all2 (memi_agree sm') im tcm.
Proof.
  move => sm sm' im.
  generalize dependent sm; generalize dependent sm'.
  induction im; move => sm' sm tcm HLen HA Hext => //=; destruct tcm => //=.
  simpl in HA. remove_bools_options.
  apply/andP; split => //=; last by eapply IHim; eauto.
  eapply memi_agree_extension; eauto.
Qed.

Lemma tabi_agree_extension: forall t0 t1 n t,
  size t0 <= size t1 ->
  tabi_agree t0 n t ->
  all2 table_extension t0 (List.firstn (length (t0)) t1) ->
  tabi_agree t1 n t.
Proof.
  move => t0 t1 n t HLen H1 H2.
  assert (size t0 = size (List.firstn (length (t0)) t1)) as HSize;
    first by eapply all2_size; eauto.
  unfold tabi_agree.
  unfold tabi_agree in H1. unfold table_extension in H2.
  induction t, t0, t1 => //=;
    first by unfold lookup_N in H1; rewrite nth_error_nil in H1 => //=.
  simpl in H2. simpl in H1.
  remove_bools_options.
  unfold tab_typing in H4.
  remove_bools_options.
  simpl in H1.
  unfold tab_typing. simpl.
  inversion HSize. subst. clear HSize.
  unfold option_map.
  assert (List.nth_error (t1 :: t2) (N.to_nat n) <> None).
  {
    apply List.nth_error_Some. rewrite length_is_size. simpl.
    simpl in HLen. assert (lookup_N (t::t0) n <> None) as Hn => //=.
    rewrite Hoption => //=. apply lookup_N_Some in Hn.
    rewrite length_is_size in Hn. simpl in Hn. lias.
  }
  unfold lookup_N. unfold lookup_N in Hoption.
  destruct (List.nth_error (t1 :: t2) (N.to_nat n)) eqn:HN => //=.
  apply/eqP. f_equal.

  destruct (N.to_nat n) => //=; simpl in HN; simpl in Hoption;
  [| assert (List.nth_error t0 n0 <> None) as Ht0len;
      first by rewrite Hoption];
  [ inversion HN; inversion Hoption; subst t3 t4;
    rewrite H; f_equal; first (f_equal; apply Nat.leb_le in H2)
  | apply List.nth_error_Some in Ht0len; move/ltP in Ht0len;
    eapply all2_projection with (x2 := t4) in H0; eauto;
      last (by eapply nth_error_firstn'; eauto);
    remove_bools_options; rewrite H0; f_equal;
    first (f_equal; apply Nat.leb_le in H7)
  ]; try (apply/leP; rewrite H1; move/leP in H1; eapply le_trans; eauto);

  rewrite H3. admit. (* prove forall elements of tableinst, typing matches *)
(* Qed. *) Admitted.

Lemma tab_extension_C: forall st st' it tct,
  size st <= size st' ->
  all2 (tabi_agree st) it tct ->
  all2 table_extension st (List.firstn (length (st)) st') ->
  all2 (tabi_agree st') it tct.
Proof.
  move => st st' it.
  generalize dependent st; generalize dependent st'.
  induction it; move => st' st tct HLen HA Hext => //=; destruct tct => //=.
  simpl in HA. remove_bools_options.
  apply/andP; split => //=; last by eapply IHit; eauto.
  by eapply tabi_agree_extension; eauto.
Qed.

Lemma elem_agree_extension: forall e0 e1 n e,
  size e0 <= size e1 ->
  elemi_agree e0 n e ->
  all2 elem_extension e0 (List.firstn (length (e0)) e1) ->
  elemi_agree e1 n e.
Proof.
  move => e0 e1 n e HLen H1 H2.
  assert (size e0 = size (List.firstn (length (e0)) e1)) as HSize;
    first by eapply all2_size; eauto.
  unfold elemi_agree, option_map, elem_typing.
  unfold elemi_agree, option_map, elem_typing in H1.
  unfold elem_extension in H2.
  remove_bools_options.

  assert (lookup_N e0 n <> None);
    first by rewrite Hoption.
  apply lookup_N_Some in H1.
  repeat rewrite -length_is_size in HSize.

  assert (lookup_N e1 n <> None);
    first by apply lookup_N_Some;
    repeat rewrite -length_is_size in HLen; lias.
  destruct (lookup_N e1 n) eqn:E1 => //=.
  apply/eqP. f_equal. f_equal. f_equal.

  remember H1 as H'. clear HeqH'.
  rewrite HSize in H1. apply lookup_N_Some in H1.
  unfold lookup_N in H1.
  
  eapply all2_projection in H2; eauto;
    last eapply nth_error_firstn'; eauto.
  move/eqP in H0. subst.
  remove_bools_options => //=.
  admit. admit.
  (* only eleminst_elem used in elem_extension *)
  (* only eleminst_type used in elemi_agree *)
  rewrite H0. admit.
Admitted.

Lemma elem_extension_C: forall se se' ie tce,
  size se <= size se' ->
  all2 (elemi_agree se) ie tce ->
  all2 elem_extension se (List.firstn (length (se)) se') ->
  all2 (elemi_agree se') ie tce.
Proof.
  move => se se' ie.
  generalize dependent se; generalize dependent se'.
  induction ie; move => se' se tce HLen HA Hext => //=; destruct tce => //=.
  - simpl in HA. remove_bools_options.
    edestruct IHie; eauto.
    remember H as H'. clear HeqH'.
    unfold elemi_agree in H. remove_bools_options.
    assert (size se = size (List.firstn (length (se)) se'));
      first by eapply all2_size; eauto.
    assert (N.to_nat a < length (List.firstn (length (se)) se'))%coq_nat.
    {
      assert (lookup_N se a <> None) as Hn. rewrite Hoption => //.
      apply lookup_N_Some in Hn.
      rewrite length_is_size in Hn. rewrite length_is_size.
      rewrite -H. rewrite <- length_is_size. by lias.
    }
    remember H1 as H5. clear HeqH5.
    rewrite <- List.nth_error_Some in H1.
    destruct (List.nth_error
        (List.firstn (length (se)) se') (N.to_nat a)) eqn:HElem => //=; eauto.
    clear H1. remember Hext as Hext1. clear HeqHext1.
    eapply all2_projection in Hext1; eauto.
    apply/andP. split => //=.
    + by eapply elem_agree_extension; eauto.
      (* unfold elemi_agree, option_map, lookup_N, elem_typing.
      assert (List.nth_error se' (N.to_nat a) = Some e0);
        first by eapply nth_error_firstn; eauto.
      unfold elemi_agree, option_map, lookup_N, elem_typing in H2.
      move/eqP in H2. rewrite H1. apply/eqP. f_equal.
      apply/andP. split => //=. admit. admit. *)
    + by eapply IHie; eauto.
Qed.

Lemma data_agree_extension: forall d0 d1 n d,
  size d0 <= size d1 ->
  datai_agree d0 n d ->
  all2 data_extension d0 (List.firstn (length (d0)) d1) ->
  datai_agree d1 n d.
Proof.
  move => d0 d1 n d HLen H1 H2.
  assert (size d0 = size (List.firstn (length (d0)) d1)) as HSize;
    first by eapply all2_size; eauto.
  unfold datai_agree, option_map.
  unfold datai_agree, option_map in H1.
  unfold data_extension in H2.
  remove_bools_options.

  assert (lookup_N d0 n <> None);
    first by rewrite Hoption.
  apply lookup_N_Some in H.
  repeat rewrite -length_is_size in HSize.

  assert (lookup_N d1 n <> None);
    first by apply lookup_N_Some;
    repeat rewrite -length_is_size in HLen; lias.
  destruct (lookup_N d1 n) eqn:D1 => //=.
Qed.

Lemma data_extension_C: forall sd sd' ie tce,
  size sd <= size sd' ->
  all2 (datai_agree sd) ie tce ->
  all2 data_extension sd (List.firstn (length (sd)) sd') ->
  all2 (datai_agree sd') ie tce.
Proof.
  move => sd sd' ie.
  generalize dependent sd; generalize dependent sd'.
  induction ie; move => sd' sd tce HLen HA Hext => //=; destruct tce => //=.
  - simpl in HA. remove_bools_options.
    edestruct IHie; eauto.
    remember H as H'. clear HeqH'.
    unfold datai_agree in H. remove_bools_options.
    assert (size sd = size (List.firstn (length (sd)) sd'));
      first by eapply all2_size; eauto.
    assert (N.to_nat a < length (List.firstn (length (sd)) sd'))%coq_nat.
    {
      assert (lookup_N sd a <> None) as Hn. rewrite Hoption => //.
      apply lookup_N_Some in Hn.
      rewrite length_is_size in Hn. rewrite length_is_size.
      rewrite -H. rewrite <- length_is_size. by lias.
    }
    remember H1 as H5. clear HeqH5.
    rewrite <- List.nth_error_Some in H1.
    destruct (List.nth_error
        (List.firstn (length (sd)) sd') (N.to_nat a)) eqn:Hdata => //=; eauto.
    clear H1. remember Hext as Hext1. clear HeqHext1.
    eapply all2_projection in Hext1; eauto.
    apply/andP. split => //=.
    + by eapply data_agree_extension; eauto.
    + by eapply IHie; eauto.
Qed.

Lemma inst_typing_extension: forall s s' i C,
    store_extension s s' ->
    inst_typing s i C ->
    inst_typing s' i C.
Proof.
  move => s s' i C HST HIT.
  unfold store_extension in HST. unfold operations.store_extension in HST.
  unfold inst_typing in HIT. unfold typing.inst_typing in HIT.
  unfold inst_typing. unfold typing.inst_typing.
  destruct i, C, tc_local, tc_label, tc_return, tc_ref => //.
  remove_bools_options.
  unfold component_extension in H6. move/andP in H6. destruct H6 as [Hfl Hf].
  unfold component_extension in H7. move/andP in H7. destruct H7 as [Hdl Hd].
  unfold component_extension in H8. move/andP in H8. destruct H8 as [Hel He].
  unfold component_extension in H9. move/andP in H9. destruct H9 as [Hgl Hg].
  unfold component_extension in H10. move/andP in H10. destruct H10 as [Hml Hm].
  unfold component_extension in H11. move/andP in H11. destruct H11 as [Htl Ht].
  repeat (apply/andP; split => //=; subst => //=).
  
  - eapply func_extension_C with (sf := (s_funcs s)); eauto.
    apply Nat.leb_le in Hfl. lias.
  - eapply global_extension_C with (sg := (s_globals s)); eauto.
    apply Nat.leb_le in Hgl. lias.
  - eapply tab_extension_C with (st := (s_tables s)); eauto.
    apply Nat.leb_le in Htl. lias.
  - eapply mem_extension_C with (sm := (s_mems s)); eauto.
    apply Nat.leb_le in Hml. lias.
  - eapply elem_extension_C with (se := (s_elems s)); eauto.
    apply Nat.leb_le in Hel. lias.
  - eapply data_extension_C with (sd := (s_datas s)); eauto.
    apply Nat.leb_le in Hdl. lias.
Qed.

Lemma frame_typing_extension: forall s s' f C,
    store_extension s s' ->
    frame_typing s f C ->
    frame_typing s' f C.
Proof.
  move => s s' f C HST HIT.
  unfold store_extension in HST. unfold operations.store_extension in HST.
  inversion HIT. subst.
  eapply inst_typing_extension in H; eauto.
  by eapply mk_frame_typing; eauto.
Qed.

Lemma reflexive_all2_same: forall {X:Type} f (l: seq X),
    reflexive f ->
    all2 f l l.
Proof.
  move => X f l.
  induction l; move => H; unfold reflexive in H => //=.
  apply/andP. split => //=.
  by apply IHl.
Qed.

Lemma all2_func_extension_same: forall t,
    all2 (@func_extension host_function) t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive.
  move => x. unfold func_extension => //=.
Qed.

Lemma all2_table_extension_same: forall t,
    all2 table_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive. move => x. unfold table_extension.
  apply/andP. split => //=. destruct x. unfold tab_size. simpl.
  induction (length tableinst_elem) => //=.
Qed.

Lemma all2_mem_extension_same: forall t,
    all2 mem_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive. move => x. unfold mem_extension.
  apply/andP; split => //.
  by apply N.leb_le; lias.
Qed.

Lemma all2_global_extension_same: forall t,
    all2 global_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive. move => x.
  unfold global_extension. apply/andP; split => //.
  destruct (g_type x) => //=. apply/orP. by right.
Qed.

Lemma all2_elem_extension_same: forall t,
    all2 elem_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive. move => x.
  unfold elem_extension. apply/orP; by left.
Qed.

Lemma all2_data_extension_same: forall t,
    all2 data_extension t t.
Proof.
  move => t.
  apply reflexive_all2_same. unfold reflexive. move => x.
  unfold data_extension. apply/orP; by left.
Qed.

Ltac convert_et_to_bet:=
  lazymatch goal with
  | H: e_typing _ _ _ _ |- _ =>
    apply et_to_bet in H; try auto_basic; simpl in H
  end.

(* TODO: find better fixes than the current duplication. *)
Ltac split_et_composition:=
  lazymatch goal with
  (* e_composition_typing_all_not_basic exists but not sure how to match *)
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
  | H: e_typing _ _ ((v_to_e_list _) ++ _) _ |- _ =>
    let t3s := fresh "t3s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply e_composition_typing_const_list in H;
    destruct H as [t3s [H1 H2]]; subst
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
  | H: typing.e_typing _ _ ((v_to_e_list _) ++ _) _ |- _ =>
    let t3s := fresh "t3s" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply e_composition_typing_const_list in H;
    destruct H as [t3s [H1 H2]]; subst
  end.

Ltac invert_e_typing_step:=
  lazymatch goal with
  | H: typing.e_typing _ _ _ _ |- _ =>
    fold e_typing in H
  | H: e_typing _ _ [::] _ |- _ =>
    apply e_empty_typing in H; subst
  | H: e_typing _ _ [::$VAN _] _ |- _ =>
    apply AI_const_num_typing in H; subst
  | H: e_typing _ _ [::AI_basic (BI_const_vec _)] _ |- _ =>
    apply AI_const_vec_typing in H; subst
  | H: e_typing _ _ [::AI_basic (BI_ref_null _)] _ |- _ =>
    apply AI_ref_null_typing in H; subst
  | H: e_typing _ _ [::AI_ref _] _ |- _ =>
    let tf := fresh "tf" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    apply AI_ref_func_typing in H; destruct H as [tf [H1 H2]]; subst
  | H: e_typing _ _ [::AI_ref_extern _] _ |- _ =>
    apply AI_ref_extern_typing in H; subst
  (* Unsure how to check for multiple related hypotheses *)
  (* This pattern will stop checking other matches on failure
  | H: e_typing _ _ xxxx _ |- _ =>
    lazymatch goal with
    | H': supporting hyp |- _ =>
      apply xxxx_typing in H; subst
    end
  *)
  (*
  | H: e_typing _ _ [::AI_invoke _] _ |- be_typing _ _ _ =>
    let ts' := fresh "ts'" in
    let C' := fresh "C" in
    let H1 := fresh "H1" in
    let H2 := fresh "H2" in
    let H3 := fresh "H3" in
    let H4 := fresh "H4" in
    eapply Invoke_func_native_typing in H; eauto;
    destruct H as [ts' [C' [H1 [H2 [H3 H4]]]]]; subst
  *)
  | H: e_typing _ _ [:: v_to_e ?v] _ |- _ =>
    let Hf := fresh "Hf" in
    apply const_typing in H; last (by apply v_to_e_is_const);
    destruct H as [Hf H]; subst
  | H: e_typing _ _ (v_to_e_list ?vs) _ |- _ =>
    let Hf := fresh "Hf" in
    apply const_list_typing in H; last (by apply v_to_e_is_const_list);
    destruct H as [Hf H]; subst
  | H: e_typing _ _ (_ ++ _) _ |- _ =>
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
  | H: e_typing _ _ [::_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: e_typing _ _ [::_;_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: e_typing _ _ [::_;_;_;_] _ |- _ =>
    rewrite -cat1s in H
  | H: _ ++ [::_] = _ ++ [::_] |- _ =>
    apply concat_cancel_last in H; destruct H; subst
  end.
Ltac invert_e_typing:=
  repeat invert_e_typing_step.


Lemma lfilled_es_type_exists: forall k lh es les s C tf,
    @lfilled k lh es les ->
    e_typing s C les tf ->
    exists lab t1s t2s, e_typing s (upd_label C lab) es (Tf t1s t2s).
Proof.
  move => k lh es les s C tf HLF HType.
  generalize dependent tf.
  generalize dependent C.
  generalize dependent s.
  dependent induction lh; move => s C tf HType;
  unfold lfilled in HLF; simpl in HLF; destruct tf;
  move/eqP in HLF; rewrite <- HLF in HType.
  - invert_e_typing.
    exists (tc_label C), t1s0, t3s => //=.
    by rewrite upd_label_unchanged.
  - unfold lfilled.
    rewrite -cat1s catA in HType.
    invert_e_typing.
    unfold lfilled in IHlh.
    edestruct IHlh; eauto.
Qed.

Lemma store_extension_same: forall s,
    store_extension s s.
Proof.
  move => s. unfold store_extension. unfold operations.store_extension.
  repeat (apply/andP; split).
  - induction s_funcs => //=.
  - rewrite List.firstn_all. apply all2_func_extension_same.
  - induction s_tables => //=.
  - rewrite List.firstn_all. apply all2_table_extension_same.
  - repeat fold s_mems. induction s_mems => //=.
  - repeat fold s_mems. rewrite List.firstn_all. apply all2_mem_extension_same.
  - repeat fold s_globals. induction s_globals => //=.
  - repeat fold s_globals. rewrite List.firstn_all. apply all2_global_extension_same.
  - induction s_elems => //=.
  - rewrite List.firstn_all. apply all2_elem_extension_same.
  - induction s_datas => //=.
  - rewrite List.firstn_all. apply all2_data_extension_same.
Qed.

(* This is the only questionable lemma that I'm not >99% sure of it's correctness.
   But it seems to be absolutely required. Maybe I'm 98% sure. *)
(*
   UPD: oops, this is in fact completely nonsense and in no way required --
          I overlooked another possibility here. This is now abandoned and
          replaced by a correct version.

Lemma store_reduce_same_es_typing: forall s vs es i s' vs' es' es0 C C' loc lab ret tf,
    reduce s vs es i s' vs' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s i C ->
    inst_typing s' i C' ->
    e_typing s (upd_label (upd_local_return C loc ret) lab) es0 tf ->
    e_typing s' (upd_label (upd_local_return C' loc ret) lab) es0 tf.
Proof.
 *)

Lemma store_extension_cl_typing: forall s s' cl tf,
    store_extension s s' ->
    cl_typing s cl tf ->
    cl_typing s' cl tf.
Proof.
  move => s s' cl tf Hext HType.
  inversion HType; subst.
  - eapply cl_typing_native; eauto.
    by eapply inst_typing_extension; eauto.
  - by eapply cl_typing_host; eauto.
Qed.

(*
  The correct version. We need a mutual induction on e_typing and s_typing
    since they were defined with a mutual induction.
 *)

Lemma store_extension_e_typing: forall s s' C es tf,
    store_typing s ->
    store_typing s' ->
    store_extension s s' ->
    e_typing s C es tf -> e_typing s' C es tf.
Proof.
  move=> s s' C es tf HST1 HST2 Hext HType. move: s' HST1 HST2 Hext.
  apply e_typing_ind' with (e := HType)
    (P := fun s C es tf (_ : e_typing s C es tf) => forall s',
            store_typing s ->
            store_typing s' ->
            store_extension s s' ->
            e_typing s' C es tf)
    (P0 := fun s rs f es ts (_ : s_typing s rs f es ts) => forall s',
             store_typing s ->
             store_typing s' ->
             store_extension s s' ->
             s_typing s' rs f es ts); clear HType s C es tf.
  - move=> s C bes tf HType s' HST1 HST2 Hext.
    apply ety_a'; first by apply to_e_list_basic.
    replace (operations.to_b_list (operations.to_e_list bes)) with bes => //.
    by apply b_e_elim.
  - move=> s C bes tf r1 r2 r3 HType1 IHHType1 IH2 IHHType2 s' HST1 HST2 Hext.
    eapply ety_composition.
    + by apply IHHType1.
    + by apply IHHType2.
  - move=> s C es tf t1s t2s HType IHHType s' HST1 HST2 Hext.
    eapply ety_weakening. by apply IHHType.
  - move=> s C tf s' HST1 HST2 Hext.
    by apply ety_trap.
  - move=> s C tf s' HST1 HST2 Hext.
    by apply ety_ref_extern.
  - move=> s C a tf Hf s' HST1 HST2 Hext.
    unfold store_extension, operations.store_extension in Hext.
    remove_bools_options.
    unfold component_extension, func_extension in H.
    remove_bools_options.
    unfold funci_agree, option_map, lookup_N in Hf.
    remove_bools_options.

    eapply all2_func_projection with (x2 := f) in H5; eauto.
    eapply ety_ref with (tf := cl_type f); eauto.
    unfold funci_agree, option_map, lookup_N.

    assert (List.nth_error (s_funcs s) (N.to_nat a) <> None);
      first by rewrite Hoption.
    apply List.nth_error_Some in H6.
    move/ltP in H6. apply Nat.leb_le in H. move/leP in H.
    assert (N.to_nat a < length (s_funcs s')); first by lias.

    assert (List.nth_error (s_funcs s') (N.to_nat a) = Some f);
      last by rewrite H8.
    
    eapply nth_error_firstn with (lim := (length (s_funcs s))); eauto.
  - move=> s a C cl tf HNth HCLType s' HST1 HST2 Hext.
    assert (cl_typing s' cl tf);
      first by eapply store_extension_cl_typing; eauto.    
    eapply ety_invoke; eauto => //.

    unfold store_extension, operations.store_extension in Hext.
    remove_bools_options. unfold component_extension in H0.
    remove_bools_options. unfold lookup_N.
    assert (lookup_N (s_funcs s) a <> None); first by rewrite HNth.
    apply lookup_N_Some in H7. apply Nat.leb_le in H0. move/leP in H0.
    eapply nth_error_firstn with (lim := length (s_funcs s)); eauto.
    eapply all2_func_projection; eauto.
  - move=> s C es es' t1s t2s n HType1 IHHType1 HType2 IHHType2 E s' HST1 HST2 Hext.
    eapply ety_label => //; eauto.
    + by apply IHHType1.
    + by apply IHHType2.
  - move=> s C n f es ts HType IHHType E s' HST1 HST2 Hext.
    apply ety_local => //.
    by eapply IHHType; try apply HST1 => //.
  - move=> s f es rs ts C C' HFType HContext HType IHHType E' s' HST1 HST2 Hext.
    eapply mk_s_typing; eauto.
    + by eapply frame_typing_extension; eauto.
    + by apply IHHType.
Qed.

Lemma tc_reference_glob_type: forall s i C n m gt g,
    inst_typing s i C ->
    lookup_N (inst_globals i) n = Some m ->
    lookup_N (s_globals s) m = Some g ->
    lookup_N (tc_global C) n = Some gt ->
    gt = g_type g.
Proof.
  move => s i C n m gt g HIT HN1 HN2 HN3.
  unfold inst_typing in HIT. unfold typing.inst_typing in HIT.
  destruct i, C, tc_local, tc_label, tc_return, tc_ref => //=.
  move/andP in HIT. destruct HIT.
  repeat (move/andP in H; destruct H).
  simpl in HN1. simpl in HN2.
  remove_bools_options.
  eapply all2_projection in H4; eauto.
  unfold globali_agree, global_typing in H4.
  unfold s_globals in HN2.
  by remove_bools_options.
Qed.

Lemma global_extension_update_nth: forall sglobs n g g',
  List.nth_error sglobs n = Some g ->
  global_extension g g' ->
  all2 global_extension sglobs (set_nth g' sglobs n g').
Proof.
  move => sglobs n.
  generalize dependent sglobs.
  induction n; move => sglobs g g' HN Hext => //=; destruct sglobs => //.
  - simpl in HN. inversion HN. subst.
    apply/andP; split => //=.
    by apply all2_global_extension_same.
  - assert ((n.+1 < length (g0 :: sglobs))%coq_nat); first by rewrite -List.nth_error_Some; rewrite HN.
    simpl.
    apply/andP. split.
    + unfold global_extension. apply/andP. split => //=.
      destruct (g_type g0) => //=. apply/orP. by right.
    + by eapply IHn; eauto.
Qed.

Lemma mem_extension_update_nth: forall smems n m m',
  List.nth_error smems n = Some m ->
  mem_extension m m' ->
  all2 mem_extension smems (set_nth m' smems n m').
Proof.
  move => smems n.
  generalize dependent smems.
  induction n; move => smems m m' HN Hext => //=; destruct smems => //.
  - simpl in HN. inversion HN. subst.
    apply/andP. split; first apply Hext.
    by apply all2_mem_extension_same.
  - assert ((n.+1 < length (m0 :: smems))%coq_nat); first by rewrite -List.nth_error_Some; rewrite HN.
    simpl.
    apply/andP. split.
    + unfold mem_extension. apply/andP; split => //.
      apply N.leb_le; by lias.
    + by eapply IHn; eauto.
Qed.

Lemma table_extension_update_nth: forall stabs n m m',
  List.nth_error stabs n = Some m ->
  table_extension m m' ->
  all2 table_extension stabs (set_nth m' stabs n m').
Proof.
  move => stabs n.
  generalize dependent stabs.
  induction n; move => stabs m m' HN Hext => //=; destruct stabs => //.
  - simpl in HN. inversion HN. subst.
    apply/andP. split; first apply Hext.
    by apply all2_table_extension_same.
  - assert ((n.+1 < length (t :: stabs))%coq_nat); first by rewrite -List.nth_error_Some; rewrite HN.
    simpl.
    apply/andP. split.
    + unfold table_extension. apply/andP; split => //.
      apply Nat.leb_le; by lias.
    + by eapply IHn; eauto.
Qed.

Lemma elem_extension_update_nth: forall selems n e e',
  List.nth_error selems n = Some e ->
  elem_extension e e' ->
  all2 elem_extension selems (set_nth e' selems n e').
Proof.
  move => selems n.
  generalize dependent selems.
  induction n; move => selems m m' HN Hext => //=; destruct selems => //.
  - simpl in HN. inversion HN. subst.
    apply/andP. split; first apply Hext.
    by apply all2_elem_extension_same.
  - assert ((n.+1 < length (e :: selems))%coq_nat);
      first by rewrite -List.nth_error_Some; rewrite HN.
    simpl. apply/andP. split.
    + unfold elem_extension. apply/orP; left => //.
    + by eapply IHn; eauto.
Qed.

Lemma data_extension_update_nth: forall sdatas n d d',
  List.nth_error sdatas n = Some d ->
  data_extension d d' ->
  all2 data_extension sdatas (set_nth d' sdatas n d').
Proof.
  move => sdatas n.
  generalize dependent sdatas.
  induction n; move => sdatas m m' HN Hext => //=; destruct sdatas => //.
  - simpl in HN. inversion HN. subst.
    apply/andP. split; first apply Hext.
    by apply all2_data_extension_same.
  - assert ((n.+1 < length (d :: sdatas))%coq_nat);
      first by rewrite -List.nth_error_Some; rewrite HN.
    simpl. apply/andP. split.
    + unfold data_extension. apply/orP; left => //.
    + by eapply IHn; eauto.
Qed.

Lemma bytes_takefill_size: forall c l vs,
    size (bytes_takefill c l vs) = l.
Proof.
  move => c l. induction l => //=.
  by destruct vs => //=; f_equal.
Qed.

Lemma bytes_replicate_size: forall n b,
    size (bytes_replicate n b) = n.
Proof.
  induction n => //=.
  by move => b; f_equal.
Qed.

Lemma div_le: forall a b, b > 0 -> a/b <= a.
Proof.
  move => a b H.
  destruct b => //.
  destruct b => //; first by rewrite Nat.div_1_r; lias.
  destruct a => //.
  assert (a.+1/b.+2 < a.+1)%coq_nat.
  { by apply Nat.div_lt; lias. }
  by lias.
Qed.

(* Start of proof to write_bytes preserving memory type *)

Lemma list_fold_left_rev_prop: forall {X Y: Type} P f (l: seq X) (a1 a2: Y),
    List.fold_left f l a1 = a2 ->
    P a2 ->
    (forall a e a', P a' -> f a e = a' -> P a) ->
    P a1.
Proof.
  move => X Y P f l.
  elim: l => //=.
  - move => a1 a2 H. by subst.
  - move => e l IH a1 a2 HFold HP HNec.
    assert (HPF: P (f a1 e)); first by eapply IH; eauto.
    by eapply HNec; eauto.
Qed.
    
Lemma list_fold_left_restricted_trans: forall {X Y: Type} P R f (l: seq X) (a1 a2: Y),
    List.fold_left f l a1 = a2 ->
    P a1 ->
    P a2 ->
    (forall a e a', P a -> P a' -> f a e = a' -> R a a') ->
    (forall a, P a -> R a a) ->
    (forall a1 a2 a3, P a1 -> P a2 -> P a3 -> R a1 a2 -> R a2 a3 -> R a1 a3) ->
    (forall a e a', P a' -> f a e = a' -> P a) ->
    R a1 a2.
Proof.
  move => X Y P R f l.
  elim: l => //=.
  - move => a1 a2 H HP1 HP2 HF HRefl HTrans HNec. subst.
    by apply HRefl.
  - move => e l IH a1 a2 HFold HP1 HP2 HF HRefl HTrans HNec.
    assert (HPF: P (f a1 e)); first by eapply list_fold_left_rev_prop; eauto.
    assert (HRf2: R (f a1 e) a2); first by apply IH.
    assert (HR1f: R a1 (f a1 e)); first by eapply HF; eauto.
    by eapply HTrans; eauto.
Qed.
    
Definition proj2_some (acc: nat * option memory_list.memory_list) : Prop :=
  let (n, om) := acc in
  exists m, om = Some m.

Definition mem_type_proj2_preserve (acc1 acc2: nat * option memory_list.memory_list) : Prop :=
  let (n1, om1) := acc1 in
  let (n2, om2) := acc2 in
  (exists m1 m2,
      om1 = Some m1 /\
      om2 = Some m2 /\
      memory_list.mem_length m1 = memory_list.mem_length m2).

Lemma mem_type_proj2_preserve_trans: forall a1 a2 a3,
    proj2_some a1 ->
    proj2_some a2 ->
    proj2_some a3 ->
    mem_type_proj2_preserve a1 a2 ->
    mem_type_proj2_preserve a2 a3 ->
    mem_type_proj2_preserve a1 a3.
Proof.
  unfold mem_type_proj2_preserve, proj2_some.
  move => a1 a2 a3 HP1 HP2 HP3 HR12 HR23.
  destruct a1, a2, a3 => /=.
  destruct HP1, HP2, HP3, HR12, HR23. subst.
  repeat eexists; eauto.
  destruct H2 as [m2 [H21 [H22 HLen1]]].
  destruct H3 as [m2' [H31 [H32 HLen2]]].
  inversion H21. inversion H22. inversion H31. inversion H32. subst.
  by lias.
Qed.

Lemma write_bytes_preserve_type: forall m pos str m',
  write_bytes m pos str = Some m' ->
  (mem_size m = mem_size m') /\ (meminst_type m = meminst_type m').
Proof.
  unfold write_bytes, fold_lefti.
  move => m pos str m' H.
  remove_bools_options.
  match goal with | H : ?T = _ |- _ =>
                    match T with context [List.fold_left ?f ?str ?nom] => remember (List.fold_left f str nom) as fold_res
                    end
  end.
  assert (HPreserve: mem_type_proj2_preserve (0, Some (meminst_data m)) fold_res).
  symmetry in Heqfold_res.
  destruct fold_res; subst.
  eapply list_fold_left_restricted_trans with (P := proj2_some); unfold proj2_some; eauto.
  - move => a e a' HP1 HP2 HF.
    unfold mem_type_proj2_preserve.
    destruct a as [n1 m1]. destruct a' as [n2 m2].
    destruct HP1 as [m3 HP1]; destruct HP2 as [m4 HP2].
    subst.
    repeat eexists.
    injection HF. move => H1 H2. subst. clear HF.
    (* TODO: Use mem_ax_length_constant_update to prove this after porting in the 
         parameterized memory branch *)
    unfold memory_list.mem_update in H1.
    destruct (pos + N.of_nat n1 <? N.of_nat (length (memory_list.ml_data m3)))%N eqn:HMemSize => //=.
    injection H1. move => H2. clear H1. subst.
    unfold memory_list.mem_length => /=.
    repeat rewrite length_is_size.
    repeat rewrite size_cat => /=.
    rewrite size_take. rewrite size_drop.
    apply N.ltb_lt in HMemSize.
    rewrite length_is_size in HMemSize.
    assert (N.to_nat (pos+N.of_nat n1) < size (memory_list.ml_data m3)); first by lias.
    rewrite H.
    by lias.
  - move => a HP. destruct a as [n1 m1].
    destruct HP as [m2 HP]. subst.
    unfold mem_type_proj2_preserve.
    by repeat eexists.
  - by apply mem_type_proj2_preserve_trans.
  - move => a e a' HP HF.
    destruct a as [n1 m1]. destruct a' as [n2 m2].
    destruct HP as [m3 HP]. subst.
    destruct m1; inversion HF => //=; subst.
    by eexists.
  - simpl in HPreserve. destruct fold_res. subst.
    destruct HPreserve as [m1 [m2 [H1 [H2 HLen]]]].
    inversion H1; inversion H2; subst; clear H1; clear H2.
    split => //.
    unfold mem_size, mem_length => /=.
    by rewrite HLen.
Qed.

Lemma mem_extension_store: forall m k off v tlen mem,
    store m k off (bits v) tlen = Some mem ->
    mem_extension m mem.
Proof.
  move => m k off v tlen mem HStore.
  unfold mem_extension.
  unfold store in HStore.
  destruct ((k + off + N.of_nat tlen <=? mem_length m)%N) eqn:HMemSize => //.
  remove_bools_options.
  apply write_bytes_preserve_type in HStore; destruct HStore as [H1 H2].
  apply/andP; split => //=. rewrite H2 => //=.
  apply N.leb_le. unfold mem_size in *.
  eapply N_div_le_mono' with (c := page_size);
    first by unfold page_size.
  rewrite H1. apply N.le_refl.
Qed.

Lemma mem_extension_grow_memory: forall m c mem,
    mem_grow m c = (Some mem) ->
    mem_extension m mem.
Proof.
  move => m c mem HMGrow.
  unfold mem_extension.
  unfold mem_grow in HMGrow.
  destruct (mem_size m + c <=? page_limit)%N eqn:HLP => //.
  - destruct (lim_max (meminst_type m)) eqn:HLimMax => //=.
    destruct ((mem_size m + c <=? u)%N) eqn:HLT => //.
    move : HMGrow.
    case: mem => mem_data_ mem_max_opt_ H.
    inversion H. subst. clear H.
    simpl.
    apply/andP.
    split => //.
    (* TODO: Add a lemma for size of mem_grow, and use it to prove this after porting 
         in the parameterized memory branch *)
    { unfold mem_size, mem_length, memory_list.mem_length in *.
      simpl.
      repeat rewrite length_is_size.
      rewrite size_cat.
      apply N.leb_le.
      by lias.
      }
  - inversion HMGrow; subst; clear HMGrow.
    unfold mem_size, mem_length, memory_list.mem_length.
    simpl.
    apply/andP; split => //.
    apply N.leb_le.
    repeat rewrite length_is_size.
    rewrite size_cat.
    by lias.
Qed.
  
Lemma store_invariant_extension_store_typed: forall s s',
    store_typing s ->
    store_extension s s' ->
    (s_funcs s = s_funcs s') ->
    (s_tables s = s_tables s') ->
    (s_mems s = s_mems s') ->
    store_typing s'.
Proof.
  move => s s' HST Hext HF HT.
  remember HST as HST'. clear HeqHST'.
  unfold store_typing in HST.
  unfold store_typing.
  destruct s, s' => //=.
  destruct HST.
  rewrite -> List.Forall_forall in H.
  rewrite -> List.Forall_forall in H0.
  split => //; remove_bools_options; simpl in HF; simpl in HT; subst.
  - rewrite -> List.Forall_forall. move => x HIN.
    apply H in HIN. unfold cl_type_check_single in HIN.
    destruct HIN.
    unfold cl_type_check_single.
    exists x0. by eapply store_extension_cl_typing; eauto.
  - split => //.
    + rewrite -> List.Forall_forall. move => x HIN.
      apply H0 in HIN. unfold tab_agree in HIN.
      destruct HIN.
      rewrite -> List.Forall_forall in H1.
      unfold tab_agree.
      by rewrite -> List.Forall_forall.
    + unfold store_extension in Hext. simpl in Hext.
      remove_bools_options.
      rewrite List.Forall_forall.
      move => x HIN.
      destruct HST' as [_ [_ H8]].
      rewrite -> List.Forall_forall in H8.
      apply List.In_nth_error in HIN.
      destruct HIN as [n HN].
      apply H8. by eapply List.nth_error_In; eauto.
Qed.

Lemma store_memory_extension_store_typed: forall s s',
    store_typing s ->
    store_extension s s' ->
    (s_funcs s = s_funcs s') ->
    (s_tables s = s_tables s') ->
    List.Forall mem_agree (s_mems s') ->
    store_typing s'.
Proof.
  move => s s' HST Hext HF HT HMem.
  remember HST as HST'. clear HeqHST'.
  unfold store_typing in HST.
  unfold store_typing.
  destruct s => //=.
  destruct s' => //=.
  destruct HST.
  rewrite -> List.Forall_forall in H.
  rewrite -> List.Forall_forall in H0.
  split => //; remove_bools_options; simpl in HF; simpl in HT; subst.
  - rewrite -> List.Forall_forall. move => x HIN.
    apply H in HIN. unfold cl_type_check_single in HIN.
    destruct HIN.
    unfold cl_type_check_single.
    exists x0. by eapply store_extension_cl_typing; eauto.
  - split => //.
    rewrite -> List.Forall_forall. move => x HIN.
    apply H0 in HIN. unfold tab_agree in HIN.
    destruct HIN.
    rewrite -> List.Forall_forall in H1.
    unfold tab_agree.
    by rewrite -> List.Forall_forall.
Qed.

Lemma nth_error_map: forall {X Y:Type} l n (f: X -> Y) fv,
    List.nth_error (map f l) n = Some fv ->
    exists v,
      List.nth_error l n = Some v /\
      f v = fv.
Proof.
  move => X Y l n.
  generalize dependent l.
  induction n => //=; move => l f fv HNth; destruct l => //=.
  - destruct (map f (x::l)) eqn:HMap => //=.
    inversion HNth; subst.
    simpl in HMap. inversion HMap. subst.
    by eexists.
  - destruct (map f (x::l)) eqn:HMap => //=.
    simpl in HMap. inversion HMap. subst.
    by apply IHn.
Qed.

Lemma nth_error_update_list_hit: forall {X:Type} l n {x:X},
    n < length l ->
    lookup_N (set_nth x l n x) (N.of_nat n) = Some x.
Proof.
  move => X l n.
  unfold lookup_N. rewrite Nat2N.id.
  generalize dependent l.
  induction n => //=; destruct l => //=.
  move => x' HLength.
  rewrite -ltn_predRL in HLength.
  simpl in HLength. apply IHn => //=.
Qed.

Lemma nth_error_update_list_others: forall {X:Type} l n m {x:X},
    n <> m ->
    n < length l ->
    lookup_N (set_nth x l n x) (N.of_nat m) = lookup_N l (N.of_nat m).
Proof.
  move => X l n.

  (* lookup_N must be unfolded to avoid complications *)
  move => m.
  unfold lookup_N. rewrite Nat2N.id.
  move: m.

  move: l.
  induction n => //=; move => l m x Hne HLength;
    destruct m, l => //=.
  apply IHn => //=. lias.
Qed.

Lemma Forall_update: forall {X:Type} f l n {x:X},
    List.Forall f l ->
    f x ->
    n < length l ->
    List.Forall f (set_nth x l n x).
Proof.
  move => X f l n x HA Hf HLength.
  rewrite -> List.Forall_forall in HA.
  rewrite List.Forall_forall.
  move => x0 HIN.
  apply List.In_nth_error in HIN.
  destruct HIN as [n' HN].
  assert (n' < length (set_nth x l n x))%coq_nat.
  { rewrite <- List.nth_error_Some. by rewrite HN. }
  move/ltP in H.
  destruct (n == n') eqn:H1 => //=.
  - move/eqP in H1. subst.
    (* perhaps make an equivalent lemma for List.nth_error? *)
    assert (lookup_N (set_nth x l n' x) (N.of_nat n') = Some x0) as HN'.
    unfold lookup_N. rewrite Nat2N.id => //=. 
    rewrite nth_error_update_list_hit in HN' => //=. by inversion HN'; subst.
  - move/eqP in H1.
    assert (lookup_N (set_nth x l n x) (N.of_nat n') = Some x0) as HN'.
    unfold lookup_N. rewrite Nat2N.id => //=.
    rewrite nth_error_update_list_others in HN' => //=.
    apply HA.
    by eapply List.nth_error_In; eauto.
Qed.

Lemma store_typed_mem_agree: forall s n m,
    store_typing s ->
    List.nth_error (s_mems s) n = Some m ->
    mem_agree m.
Proof.
  move => s n m HST HN.
  unfold store_typing in HST.
  destruct s => //=.
  destruct HST as [_ [_ H]].
  rewrite -> List.Forall_forall in H.
  simpl in HN.
  apply H. by eapply List.nth_error_In; eauto.
Qed.

Lemma store_mem_agree: forall s n m k off vs tl mem,
    store_typing s ->
    List.nth_error (s_mems s) n = Some m ->
    store m k off vs tl = Some mem ->
    tl > 0 ->
    mem_agree mem.
Proof.
  move => s n m k off vs tl mem HST HN HStore HTL.
  unfold store in HStore.
  destruct ((k+off+N.of_nat tl <=? mem_length m)%N) eqn:H => //=.
  apply write_bytes_preserve_type in HStore.
  destruct HStore as [HMemSize HMemLim].
  assert (mem_agree m); first by eapply store_typed_mem_agree; eauto.
  unfold mem_agree in H0. rewrite HMemLim in H0.
  unfold mem_agree => //=.
  destruct (lim_max (meminst_type mem)) eqn:HLimMax => //=.
  by rewrite HMemSize in H0.
Qed.

Lemma inj_compare a a' :
 (a ?= a')%N = (N.to_nat a ?= N.to_nat a').
Proof.
 destruct a as [|p], a' as [|p']; simpl; trivial.
 - now destruct (Pos2Nat.is_succ p') as (n,->).
 - now destruct (Pos2Nat.is_succ p) as (n,->).
 - apply Pos2Nat.inj_compare.
Qed.
Lemma inj_div n m :
  N.to_nat (n / m) = N.to_nat n / N.to_nat m.
Proof.
  destruct m as [|m]; [now destruct n|].
  apply Nat.div_unique with (N.to_nat (n mod (N.pos m))).
  - apply Nat.compare_lt_iff. rewrite <- inj_compare.
    now apply N.mod_lt.
  - now rewrite <- N2Nat.inj_mul, <- N2Nat.inj_add, <- N.div_mod.
Qed.

Lemma mem_grow_mem_agree: forall s n m c mem,
    store_typing s ->
    List.nth_error (s_mems s) n = Some m ->
    mem_grow m c = Some mem ->
    mem_agree mem.
Proof.
  move => s n m c mem HST HN HGrow.
  assert (mem_agree m); first by eapply store_typed_mem_agree; eauto.
  unfold mem_grow in HGrow.
  unfold mem_agree. simpl.
  unfold mem_agree in H.
  destruct (mem_size m + c <=? page_limit)%N eqn:HLP => //.
  destruct (lim_max (meminst_type m)) eqn:HLimMax => //=;
    last by inversion HGrow; destruct lim_max => //=.
  destruct ((mem_size m + c <=? u)%N) eqn:H1 => //.
  inversion HGrow. unfold mem_size, mem_length, memory_list.mem_length in *.
  simpl in *. subst. clear HGrow.
  rewrite length_is_size. rewrite size_cat.
  repeat rewrite - length_is_size. rewrite List.repeat_length.
  rewrite - N.div_add in H1 => //.
  apply N.leb_le in H1.
  rewrite HLimMax Nat2N.inj_add N2Nat.id.
  apply shift_scope_le_N => //=.
  (* really close to hypothesis, just need to move <= into scope *) 

  (* Attempted to sidestep this scope change but not enough info in others *)
  (* Set Printing Coercions.
  rewrite -nat_of_bin_is_N_to_nat inj_div Nat2N.id in H.
  rewrite N.div_add in H1 => //.
  rewrite -nat_of_bin_is_N_to_nat inj_div
            N2Nat.inj_add N2Nat.inj_mul Nat2N.id Nat.div_add => //.
  replace ((length (memory_list.ml_data (meminst_data m))
            / N.to_nat page_size + N.to_nat c)%coq_nat)
     with (length (memory_list.ml_data (meminst_data m))
            / N.to_nat page_size + N.to_nat c) => //.
  Set Printing Coercions. *)
     
  (* unfold is_true. apply/leP.
  apply/(eqP (((N.of_nat (length (memory_list.ml_data (meminst_data m))) + 
                c * page_size) / page_size)%N <= u) (true)). apply H1.
  replace (((N.of_nat (length (memory_list.ml_data (meminst_data m))) + c * page_size) / page_size)%N <= u)
      with ((N.of_nat (length (memory_list.ml_data (meminst_data m))) + c * page_size) / page_size).
  replace (N.of_nat (length (memory_list.ml_data (meminst_data m)) + N.to_nat (c * page_size)))
      with ((N.of_nat (length (memory_list.ml_data (meminst_data m))) + c * page_size)).
  lias. *)
Qed.

Lemma reduce_inst_unchanged: forall hs s f es hs' s' f' es',
    reduce hs s f es hs' s' f' es' ->
    f.(f_inst) = f'.(f_inst).
Proof.
  move => hs s f es hs' s' f' es' HReduce.
  by induction HReduce.
Qed.

Lemma store_extension_reduce: forall s f es s' f' es' C tf loc lab ret hs hs',
    reduce hs s f es hs' s' f' es' ->
    inst_typing s f.(f_inst) C ->
    e_typing s (upd_label (upd_local_label_return C loc (tc_label C) ret) lab) es tf ->
    store_typing s ->
    store_extension s s' /\ store_typing s'.
Proof.
  move => s f es s' f' es' C tf loc lab ret hs hs' HReduce.
  generalize dependent C. generalize dependent tf.
  generalize dependent loc. generalize dependent lab. generalize dependent ret.
  induction HReduce => //; try move => ret lab loc tf C HIT HType HST;
  try intros; destruct tf; try by (split => //; apply store_extension_same).
  - (* invoke *)
    destruct host_instance.
    split.
    + by eapply host_application_extension; eauto.
    + by eapply host_application_typing; eauto.
  - (* update glob *)
    invert_e_typing. subst.
    apply et_to_bet in H4; auto_basic. simpl in H4.
    invert_be_typing. simpl in H1.
    unfold supdate_glob, option_bind, supdate_glob_s, option_map in H.
    assert (store_extension s s') as Hext;
      last by split => //=; eapply store_invariant_extension_store_typed;
      eauto; destruct s, s' => //=; remove_bools_options.
    
    (* Working out left here for future reference *)
    (* supdate_glob s (f_inst f) (N.to_nat i) v = Some s' *)
    (* sglob_ind s (f_inst f) (N.to_nat i) = Some y ->
       supdate_glob_s s y v = Some s'
     *)
    (* sglob_ind s (f_inst f) (N.to_nat i) = Some y ->
       lookup_N (s_globals s) y = Some a ->
       g' = {g_type := g_type a; g_val := v} ->
       s' = s with s_globals := set_nth g' (s_globals s) (N.to_nat y) g'
     
       (s_global index) y = g0,
       (s_global inst (for replaced type)) a = g1,
        (s_global type) g_type g1 = g,
        (type + value) tg_t g = typeof v,
       s' value expanded
     *)
    remove_bools_options.
    unfold sglob_ind in Hoption.
    rename H1 into Hg. rename H3 into Hmutg.
    remember Hg as Htc. clear HeqHtc.
    eapply tc_reference_glob_type in Hg; eauto.
    destruct g => //.
    destruct g1 => //. simpl in H2.
    destruct g_type => //=.
    inversion Hg. subst tg_mut0 tg_t0 tg_t. clear Hg.
    unfold is_mut in Hmutg. simpl in Hmutg.
    remove_bools_options. subst.
    assert (lookup_N (datatypes.s_globals s) g0 <> None);
      first by rewrite Hoption0. apply lookup_N_Some in H.
    unfold store_extension => //=.
    remember g0 as gv_ind.
    remember {| tg_mut := MUT_var; tg_t := typeof v |} as gv_type.
    remember {| g_type := gv_type; g_val := g_val |} as gv_inst. subst g0.
    repeat (apply/andP; split) => //=;
    try apply Nat.leb_refl; try (rewrite List.firstn_all).
    + apply all2_func_extension_same.
    + apply all2_table_extension_same.
    + apply all2_mem_extension_same.
    + repeat rewrite length_is_size. rewrite size_set_nth. unfold maxn.
      destruct ((N.to_nat gv_ind).+1 < (size (datatypes.s_globals s))) eqn:Emax.
      - apply Nat.leb_refl.
      - apply Nat.leb_le. apply/leP.
        rewrite leqNgt. intros. rewrite Emax => //=.
    + (* g_val is the old value, v is the new one, g' new inst *)
      remember {| g_type := gv_type; g_val := v |} as g'.
      rewrite List.firstn_all2.

      (* s_funcs = tc_func *)
      unfold inst_typing, typing.inst_typing in HIT. 
      destruct (f_inst f), C => //=.
      (* inst_globals, s_globals, tc_global *)
      destruct tc_local,
              tc_label, tc_return, tc_ref => //=.
      remove_bools_options. simpl in *.
      unfold lookup_N in Hoption0, Htc. simpl in Htc.
      (* for case of g', g_inst:
          g_type g' == g_type g_inst is known
          and g_type g' == MUT_var is known
         else trivial
       *)
      eapply global_extension_update_nth with (g := gv_inst) => //=.
      unfold global_extension. apply/andP. split => //=;
        first by rewrite Heqgv_inst Heqg'.
      destruct gv_inst => //=. inversion Heqgv_inst.
      destruct gv_type => //=. inversion Heqgv_type.
      apply/orP. by left.

      repeat rewrite length_is_size. rewrite size_set_nth. unfold maxn.
      destruct ((N.to_nat gv_ind).+1 < (size (datatypes.s_globals s))) eqn:Emax.
      - apply Nat.le_refl.
      - apply/leP => //=.
    + apply all2_elem_extension_same.
    + apply all2_data_extension_same.
  
  { (* table_set x *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    rewrite -(cat1s (T_num T_i32)) catA in H4.
    apply concat_cancel_last in H4. destruct H4. subst.
    rewrite catA in H1.
    apply concat_cancel_last in H1. destruct H1. subst. simpl in *.

    (* H tells us how s' is obtained from s *)
    unfold stab_update, stab in H.
    (* maybe? *)
    (* assert (store_extension s (upd_s_tab s (set_nth tab' (s_tabs s) (N.to_nat i) tab'))) as Hext. *)
    (* of course this won't work, store_invariant_extension_store_typed
        assumes the tables weren't changed *)
    assert (store_extension s s') as Hext.
    {
      remove_bools_options.
      destruct (Z.to_nat (Wasm_int.Int32.unsigned i) <? tab_size t0) eqn:Etsize => //=.
      remove_bools_options.
      repeat (apply/andP; split) => //=;
      try apply Nat.leb_refl; try (rewrite List.firstn_all).
      + apply all2_func_extension_same.
      + repeat rewrite length_is_size. rewrite size_set_nth.
        unfold maxn. destruct ((N.to_nat t).+1 < size (s_tables s)) eqn:Emax;
          symmetry; symmetry; rewrite Nat.leb_le; first by apply Nat.le_refl.
        move/negP in Emax. move/negP in Emax.
        rewrite -leqNgt in Emax. by apply/leP.
      + remember {|
          tableinst_type := tableinst_type t0;
          tableinst_elem :=
            set_nth tabv (tableinst_elem t0)
              (Z.to_nat (Wasm_int.Int32.unsigned i)) tabv
        |} as t'.
  
        assert (lookup_N (s_tables s) t <> None);
          first by rewrite Hoption0.
        apply lookup_N_Some in H.
  
        replace (List.firstn (length (s_tables s)) (set_nth t' (s_tables s) (N.to_nat t) t'))
           with (set_nth t' (s_tables s) (N.to_nat t) t').
        2: {
          symmetry. apply List.firstn_all2. repeat rewrite length_is_size.
          rewrite size_set_nth. unfold maxn.
          destruct ((N.to_nat t).+1 < size (s_tables s)) eqn:Emax.
          - apply Nat.le_refl.
          - apply/leP. by rewrite length_is_size in H.
        }
        eapply table_extension_update_nth with (m := t0) => //=.
        unfold table_extension. apply/andP. split; rewrite Heqt' => //=.
        unfold tab_size. repeat rewrite length_is_size. simpl.
        rewrite size_set_nth. unfold maxn.
        destruct ((Z.to_nat (Wasm_int.Int32.unsigned i)).+1 < size (tableinst_elem t0)) eqn:Emax;
          symmetry; symmetry; rewrite Nat.leb_le; first by apply Nat.le_refl.
        move/negP in Emax. move/negP in Emax.
        rewrite -leqNgt in Emax. by apply/leP.
      + apply all2_mem_extension_same.
      + apply all2_global_extension_same.
      + apply all2_elem_extension_same.
      + apply all2_data_extension_same.
    }

    split => //=. destruct s, s' => //=.

    destruct HST as [HST1 [HST2 HST3]].
    rewrite -> List.Forall_forall in HST1.
    rewrite -> List.Forall_forall in HST2.

    repeat split => //=; remove_bools_options;
    destruct (Z.to_nat (Wasm_int.Int32.unsigned i) <? tab_size t0) eqn:Etsize => //=;
    remove_bools_options => //=; eauto;
    try (
      rewrite -> List.Forall_forall; move => x' HIN;
      apply HST1 in HIN; unfold cl_type_check_single in HIN;
      destruct HIN;
      unfold cl_type_check_single;
      exists x0; by eapply store_extension_cl_typing; eauto
    ).
    remember {|
      tableinst_type := tableinst_type t0;
      tableinst_elem :=
        set_nth tabv (tableinst_elem t0)
          (Z.to_nat (Wasm_int.Int32.unsigned i)) tabv
    |} as t'.

    (* unfold store_extension, operations.store_extension in Hext.
    repeat (move/andP in Hext; destruct Hext as [Hext ?]).
    unfold component_extension in H6.
    move/andP in H6. destruct H6.
    unfold table_extension in H8.
    unfold tab_agree, tabsize_agree.
    apply all2_projection. *)

    rewrite -> List.Forall_forall. move => any_new_table HIN.
    

    (* unfold tab_agree.
    split. { unfold tabcl_agree. } 2:{ unfold tabsize_agree. } *)
    (* unfold tab_agree, tabcl_agree. *)
    apply HST2. simpl in Hoption0.

    (* all tables in the new one are in the old one? *)
    (* true for all except maybe the newly added one *)
    (* t0 = t *)


    (* apply List.In_nth_error in HIN. destruct HIN as [n Hn].
    apply List.nth_error_In with (n := n). rewrite -Hn.

    destruct ((N.to_nat t) == n) eqn:E.
    - move/eqP in E. subst n. unfold lookup_N in Hoption0.
      rewrite Hoption0. admit. (* t0 = t' *) *)
      (* t0 tableinst_type used in t' so equal so far *)
      (* t0 tableinst_elem modified by changing to tabv at i *)

    (* assert (forall X x0 (s: seq X) n,
      List.nth n s x0 = nth x0 s n). admit. *)
      admit.
    

  (*(* Old attempt with store_invariant_extension_store_typed *)
    remember {|
      tableinst_type := tableinst_type t0;
      tableinst_elem :=
        set_nth tabv (tableinst_elem t0)
          (Z.to_N (Wasm_int.Int32.unsigned i)) tabv
    |} as t'.

    simpl in Hoption0.
    assert (lookup_N s_tables t <> None);
      first by rewrite Hoption0.
    apply lookup_N_Some in H. rewrite length_is_size in H.

    (* essentially proving nothing changed at index t (t' = t0) *)
    eapply eq_from_nth.
    - rewrite size_set_nth. unfold maxn.
      destruct ((N.to_nat t).+1 < size s_tables) eqn:Emax => //=.
      move/negP in Emax. move/negP in Emax.
      rewrite -leqNgt in Emax. lias.
    - intros. instantiate (1 := t').
      rewrite nth_set_nth.
      destruct (i0 == N.to_nat t) eqn:Ei0 => //=; rewrite Ei0 => //=.
      move/eqP in Ei0.
      rewrite Ei0.
      assert (forall X x0 (s: seq X) n x,
        List.nth_error s n = Some x ->
        nth x0 s n = x). admit.
      edestruct H4 with (x0 := t') (x := t') (s := s_tables) (n := (N.to_nat t)).
      2: {
        (* H shows index is in bounds so appears at that index *)
        (* ignore the default for nth on the same index and seq *)
        assert (forall X x0 x0' (s: seq X) n,
          n < size s ->
          nth x0 s n = nth x0' s n
        ). admit.
        apply H5 => //=.
        (* either because index out of bounds (default)
            or because it appears at that index *)
      }
      unfold lookup_N in Hoption0. rewrite Hoption0.
      f_equal. rewrite Heqt'.
      (* t0 tableinst_type used in t' so equal so far *)
      (* t0 tableinst_elem modified by changing to tabv at i *)
      admit.
    *)
  }
  
  { (* table_grow *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    rewrite -(cat1s _ [:: T_num T_i32]) catA in H5.
    apply concat_cancel_last in H5. destruct H5. subst.
    rewrite catA in H0.
    apply concat_cancel_last in H0. destruct H0. subst. simpl in *.

    (* H tells us how s' is obtained from s *)
    unfold stab in H.
    unfold stab_grow, stab, growtable in H1.
    
    assert (store_extension s s') as Hext.
    {
      remove_bools_options.
      destruct ((u32_bound <=? N.of_nat (tab_size tab) +
                Z.to_N (Wasm_int.Int32.unsigned n))%N) eqn:Etsize => //.
      destruct (tableinst_type tab) eqn:Etit0.
      remember {|
        lim_min :=
          (N.of_nat (tab_size tab) +
           Z.to_N (Wasm_int.Int32.unsigned n))%N;
        lim_max := lim_max tt_limits
      |} as limits.
      destruct (limit_valid limits) => //.
      remove_bools_options.

      repeat (apply/andP; split) => //=;
      try apply Nat.leb_refl; try (rewrite List.firstn_all).
      + apply all2_func_extension_same.
      + repeat rewrite length_is_size. rewrite size_set_nth.
        unfold maxn. destruct ((N.to_nat t).+1 < size (s_tables s)) eqn:Emax;
          symmetry; symmetry; rewrite Nat.leb_le; first by apply Nat.le_refl.
        move/negP in Emax. move/negP in Emax.
        rewrite -leqNgt in Emax. by apply/leP.
      + remember {|
          tableinst_type :=
            {|
              tt_limits :=
                {|
                  lim_min :=
                    (N.of_nat (tab_size tab) +
                    Z.to_N (Wasm_int.Int32.unsigned n))%N;
                  lim_max := lim_max tt_limits
                |};
              tt_elem_type := tt_elem_type
            |};
          tableinst_elem :=
            tableinst_elem tab ++
            List.repeat tabinit
              (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned n)))
        |} as t'.
  
        assert (lookup_N (s_tables s) t <> None);
          first by rewrite Hoption0.
        apply lookup_N_Some in H.
  
        replace (List.firstn (length (s_tables s)) (set_nth t' (s_tables s) (N.to_nat t) t'))
           with (set_nth t' (s_tables s) (N.to_nat t) t').
        2: {
          symmetry. apply List.firstn_all2. repeat rewrite length_is_size.
          rewrite size_set_nth. unfold maxn.
          destruct ((N.to_nat t).+1 < size (s_tables s)) eqn:Emax.
          - apply Nat.le_refl.
          - apply/leP. by rewrite length_is_size in H.
        }
        eapply table_extension_update_nth with (m := tab) => //=.
        unfold table_extension. apply/andP. split; rewrite Heqt' => //=.
        * apply/eqP. rewrite Etit0. f_equal. destruct tt_limits.
          f_equal. simpl in Heqt'. simpl in Etit0.
          (* Etsize: (u32_bound <=?
                      N.of_nat (tab_size tab) +
                      Z.to_N (Wasm_int.Int32.unsigned n))%N = false *)
          (* goal: lim_min =
                      (N.of_nat (tab_size tab) +
                      Z.to_N (Wasm_int.Int32.unsigned n))%N *)
          (* effects of grow will be to obviously change this lim_min *)
          admit.
        * unfold tab_size. simpl. repeat rewrite length_is_size. simpl.
          rewrite size_cat. repeat rewrite -length_is_size.
          rewrite List.repeat_length.
          remember (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned n))) as n'.
          induction n' => //.
          -- rewrite addn0. by rewrite Nat.leb_refl.
          -- rewrite addnS -addn1. symmetry. symmetry.
            rewrite Nat.leb_le. apply/leP. lias.
      + apply all2_mem_extension_same.
      + apply all2_global_extension_same.
      + apply all2_elem_extension_same.
      + apply all2_data_extension_same.
    }

    split => //=. destruct s, s' => //=.

    destruct HST as [HST1 [HST2 HST3]].
    rewrite -> List.Forall_forall in HST1.
    rewrite -> List.Forall_forall in HST2.

    repeat split => //=; remove_bools_options;
    destruct ((u32_bound <=? N.of_nat (tab_size tab) +
                Z.to_N (Wasm_int.Int32.unsigned n))%N) eqn:Etsize => //;
    destruct (tableinst_type tab) eqn:Etit0;
    remember {|
      lim_min :=
        (N.of_nat (tab_size tab) +
          Z.to_N (Wasm_int.Int32.unsigned n))%N;
      lim_max := lim_max tt_limits
    |} as limits;
    destruct (limit_valid limits) => //;
    remove_bools_options => //=; eauto;
    try (
      rewrite -> List.Forall_forall; move => x' HIN;
      apply HST1 in HIN; unfold cl_type_check_single in HIN;
      destruct HIN;
      unfold cl_type_check_single;
      exists x0; by eapply store_extension_cl_typing; eauto
    ).

    remember {|
      tableinst_type :=
        {|
          tt_limits :=
            {|
              lim_min :=
                (N.of_nat (tab_size tab) +
                Z.to_N (Wasm_int.Int32.unsigned n))%N;
              lim_max := lim_max tt_limits
            |};
          tt_elem_type := tt_elem_type
        |};
      tableinst_elem :=
        tableinst_elem tab ++
        List.repeat tabinit
          (N.to_nat (Z.to_N (Wasm_int.Int32.unsigned n)))
    |} as t'.

    (* unfold store_extension, operations.store_extension in Hext.
    repeat (move/andP in Hext; destruct Hext as [Hext ?]).
    unfold component_extension in H6.
    move/andP in H6. destruct H6.
    unfold table_extension in H8.
    unfold tab_agree, tabsize_agree.
    apply all2_projection. *)

    rewrite -> List.Forall_forall. move => any_new_table HIN.

    (* unfold tab_agree.
    split. { unfold tabcl_agree. } 2:{ unfold tabsize_agree. } *)
    (* unfold tab_agree, tabcl_agree. *)
    apply HST2. simpl in Hoption0.
    (* all tables in the new one are in the old one? *)
    (* true for all except maybe the newly added one *)
    (* assert (forall X x0 (s: seq X) n,
      List.nth n s x0 = nth x0 s n). admit. *)
      admit.
  }

  - (* elem_drop *) 
    convert_et_to_bet. invert_be_typing. simpl in *.

    unfold selem_drop, selem in H.
    assert (store_extension s s') as Hext;
      last by split => //=; eapply store_invariant_extension_store_typed;
      eauto; destruct s, s' => //=; remove_bools_options => //=.
    remove_bools_options.
    repeat (apply/andP; split) => //=;
    try apply Nat.leb_refl; try (rewrite List.firstn_all).
    + apply all2_func_extension_same.
    + apply all2_table_extension_same.
    + apply all2_mem_extension_same.
    + apply all2_global_extension_same.
    + repeat rewrite length_is_size. rewrite size_set_nth.
      unfold maxn. destruct ((N.to_nat e).+1 < size (s_elems s)) eqn:Emax;
        symmetry; symmetry; rewrite Nat.leb_le; first by apply Nat.le_refl.
      move/negP in Emax. move/negP in Emax.
      rewrite -leqNgt in Emax. by apply/leP.
    + remember {| eleminst_type := eleminst_type e0;
                  eleminst_elem := [::] |} as elem.

      assert (lookup_N (s_elems s) e <> None);
        first by rewrite Hoption0.
      apply lookup_N_Some in H.

      replace (List.firstn (length (s_elems s)) (set_nth elem (s_elems s) (N.to_nat e) elem))
          with (set_nth elem (s_elems s) (N.to_nat e) elem).
      2: {
        symmetry. apply List.firstn_all2. repeat rewrite length_is_size.
        rewrite size_set_nth. unfold maxn.
        destruct ((N.to_nat e).+1 < size (s_elems s)) eqn:Emax.
        - apply Nat.le_refl.
        - apply/leP. by rewrite length_is_size in H.
      }
      eapply elem_extension_update_nth with (e := e0) => //=.
      unfold elem_extension. apply/orP. right. by rewrite Heqelem.
    + apply all2_data_extension_same.

  - (* update memory : store none *) 
    apply et_to_bet in HType; auto_basic. unfold to_b_list, map in HType.
    unfold to_b_single in HType at 1. unfold to_b_single in HType at 2.
    replace [::$VBN (VAL_int32 k); to_b_single ($VAN v); BI_store t None a off]
      with ([::$VBN (VAL_int32 k); to_b_single ($VAN v)] ++ [::BI_store t None a off]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    simpl in H5.
    invert_be_typing.
    assert (store_extension s (upd_s_mem s (set_nth mem' (s_mems s) (N.to_nat i) mem'))) as Hext.
    + unfold store_extension => //=.
      repeat (apply/andP; split) => //=;
      try apply Nat.leb_refl; try rewrite List.firstn_all => //=.
      * apply all2_func_extension_same.
      * apply all2_table_extension_same.
      * assert (lookup_N (datatypes.s_mems s) i <> None);
        first by rewrite H1. apply lookup_N_Some in H.
        repeat rewrite length_is_size. rewrite length_is_size in H.
        rewrite size_set_nth. unfold maxn.
        destruct ((N.to_nat i).+1 < size (s_mems s)) eqn:Emax;
          symmetry; symmetry; rewrite Nat.leb_le; first by apply Nat.le_refl.
        move/negP in Emax. move/negP in Emax.
        rewrite -leqNgt in Emax. by apply/leP.
      * assert (lookup_N (datatypes.s_mems s) i <> None).
        by rewrite H1. apply lookup_N_Some in H.
        rewrite List.firstn_all2. 2: {
          repeat rewrite length_is_size. rewrite length_is_size in H.
          rewrite size_set_nth. unfold maxn.
          destruct ((N.to_nat i).+1 < size (s_mems s)) eqn:Emax;
            first by apply Nat.le_refl.
          move/negP in Emax. move/negP in Emax.
          rewrite -leqNgt in Emax. by apply/leP.
        }
        eapply mem_extension_update_nth with (m := m).
        unfold lookup_N in H1 => //=.
        by eapply mem_extension_store; eauto.
      * apply all2_global_extension_same.
      * apply all2_elem_extension_same.
      * apply all2_data_extension_same.
    split => //.
    eapply store_memory_extension_store_typed; eauto => //=.
    remember HST as HST2. clear HeqHST2.
    unfold store_typing in HST.
    destruct s => //=.
    destruct HST as [_ [_ H11]].
    simpl in H1.
    assert ((N.to_nat i) < length s_mems0)%coq_nat.
    { apply List.nth_error_Some. unfold lookup_N in H1. by rewrite H1. }
    inversion H0; subst. clear H0.
    apply Forall_update => //=.
    eapply store_mem_agree; eauto.
    * by destruct v => //=.
    * by move/ltP in H.
  
  - (* another update memory : store some *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::$VBN (VAL_int32 k); $VBN v; BI_store t (Some tp) a off]
       with ([::$VBN (VAL_int32 k); $VBN v] ++ [::BI_store t (Some tp) a off]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    invert_be_typing.
    assert (store_extension s (upd_s_mem s (set_nth mem' (s_mems s) (N.to_nat i) mem'))) as Hext.
    + unfold store_extension => //=.
      repeat (apply/andP; split) => //=;
      try apply Nat.leb_refl; try rewrite List.firstn_all => //=.
      * by apply all2_func_extension_same.
      * by apply all2_table_extension_same.
      * assert (lookup_N (datatypes.s_mems s) i <> None);
        first by rewrite H1. apply lookup_N_Some in H.
        replace (datatypes.s_mems s) with (s_mems s) in * => //=.
        repeat rewrite length_is_size. rewrite length_is_size in H.
        rewrite size_set_nth. unfold maxn.
        destruct ((N.to_nat i).+1 < size (s_mems s)) eqn:Emax;
          symmetry; symmetry; rewrite Nat.leb_le; first by apply Nat.le_refl.
        move/negP in Emax. move/negP in Emax.
        rewrite -leqNgt in Emax. by apply/leP.
      * assert (lookup_N (datatypes.s_mems s) i <> None);
        first by rewrite H1. apply lookup_N_Some in H.
        rewrite List.firstn_all2. 2: {
          repeat rewrite length_is_size. rewrite length_is_size in H.
          rewrite size_set_nth. unfold maxn.
          destruct ((N.to_nat i).+1 < size (s_mems s)) eqn:Emax;
            first by apply Nat.le_refl.
          move/negP in Emax. move/negP in Emax.
          rewrite -leqNgt in Emax. by apply/leP.
        }
        eapply mem_extension_update_nth with (m := m).
        unfold lookup_N in H1 => //=.
        by eapply mem_extension_store; eauto.
      * by apply all2_global_extension_same.
      * by apply all2_elem_extension_same.
      * by apply all2_data_extension_same.
    split => //.
    eapply store_memory_extension_store_typed; eauto => //=.
    remember HST as HST2. clear HeqHST2.
    unfold store_typing in HST.
    destruct s => //=.
    destruct HST as [_ [_ H11]].
    simpl in H1.
    assert ((N.to_nat i) < length s_mems0)%coq_nat.
    { apply List.nth_error_Some. unfold lookup_N in H1. by rewrite H1. }
    apply Forall_update => //=.
    eapply store_mem_agree; eauto.
    * by destruct tp => //=.
    * by move/ltP in H.
  
  - (* again update memory : memory_grow *)
    apply et_to_bet in HType; auto_basic. simpl in HType.
    replace [::$VBN (VAL_int32 c); BI_memory_grow]
       with ([::$VBN (VAL_int32 c)] ++ [::BI_memory_grow]) in HType => //.
    apply composition_typing in HType.
    destruct HType as [ts [t1s [t2s [t3s [H3 [H4 [H5 H6]]]]]]]. subst.
    invert_be_typing.
    assert (store_extension s (upd_s_mem s (set_nth mem' (s_mems s) (N.to_nat i) mem'))) as Hext.
    + unfold store_extension => //=.
      repeat (apply/andP; split) => //=;
      try apply Nat.leb_refl; try rewrite List.firstn_all => //=.
      * by apply all2_func_extension_same.
      * by apply all2_table_extension_same.
      * assert (lookup_N (datatypes.s_mems s) i <> None);
        first by rewrite H0. apply lookup_N_Some in H3.
        replace (datatypes.s_mems s) with (s_mems s) in * => //=.
        repeat rewrite length_is_size. rewrite length_is_size in H3.
        rewrite size_set_nth. unfold maxn.
        destruct ((N.to_nat i).+1 < size (s_mems s)) eqn:Emax;
          symmetry; symmetry; rewrite Nat.leb_le; first by apply Nat.le_refl.
        move/negP in Emax. move/negP in Emax.
        rewrite -leqNgt in Emax. by apply/leP.
      * assert (lookup_N (datatypes.s_mems s) i <> None);
        first by rewrite H0. apply lookup_N_Some in H3.
        rewrite List.firstn_all2. 2: {
          repeat rewrite length_is_size. rewrite length_is_size in H3.
          rewrite size_set_nth. unfold maxn.
          destruct ((N.to_nat i).+1 < size (s_mems s)) eqn:Emax;
            first by apply Nat.le_refl.
          move/negP in Emax. move/negP in Emax.
          rewrite -leqNgt in Emax. by apply/leP.
        }
        eapply mem_extension_update_nth with (m := m).
        unfold lookup_N in H3 => //=.
        by eapply mem_extension_grow_memory; eauto.
      * by apply all2_global_extension_same.
      * by apply all2_elem_extension_same.
      * by apply all2_data_extension_same.
    split => //.
    eapply store_memory_extension_store_typed; eauto => //=.
    remember HST as HST2. clear HeqHST2.
    unfold store_typing in HST.
    destruct s => //=.
    destruct HST as [_ [_ H11]].
    simpl in H0.
    assert ((N.to_nat i) < length s_mems0)%coq_nat.
    { apply List.nth_error_Some. unfold lookup_N in H0. by rewrite H0. }
    apply Forall_update => //=.
    eapply mem_grow_mem_agree; eauto. by move/ltP in H3.

  - (* data_drop *)
    convert_et_to_bet. invert_be_typing. simpl in *.

    unfold sdata_drop, sdata in H.
    assert (store_extension s s') as Hext.
    2: {
      split => //=; eapply store_invariant_extension_store_typed;
      eauto; destruct s, s' => //=; remove_bools_options => //=.
    }
    remove_bools_options.
    repeat (apply/andP; split) => //=;
    try apply Nat.leb_refl; try (rewrite List.firstn_all).
    + apply all2_func_extension_same.
    + apply all2_table_extension_same.
    + apply all2_mem_extension_same.
    + apply all2_global_extension_same.
    + apply all2_elem_extension_same.
    + repeat rewrite length_is_size. rewrite size_set_nth.
      unfold maxn. destruct ((N.to_nat d).+1 < size (s_datas s)) eqn:Emax;
        symmetry; symmetry; rewrite Nat.leb_le; first by apply Nat.le_refl.
      move/negP in Emax. move/negP in Emax.
      rewrite -leqNgt in Emax. by apply/leP.
    + remember {| datainst_data := [::] |} as data.

      assert (lookup_N (s_datas s) d <> None);
        first by rewrite Hoption0.
      apply lookup_N_Some in H.

      replace (List.firstn (length (s_datas s)) (set_nth data (s_datas s) (N.to_nat d) data))
         with (set_nth data (s_datas s) (N.to_nat d) data).
      2: {
        symmetry. apply List.firstn_all2. repeat rewrite length_is_size.
        rewrite size_set_nth. unfold maxn.
        destruct ((N.to_nat d).+1 < size (s_datas s)) eqn:Emax.
        - apply Nat.le_refl.
        - apply/leP. by rewrite length_is_size in H.
      }
      eapply data_extension_update_nth with (d := d0) => //=.
      unfold data_extension. apply/orP. right. by rewrite Heqdata.
    
  - (* r_label *)
    eapply lfilled_es_type_exists in HType; eauto.
    destruct HType as [lab' [t1s [t2s HType]]].
    eapply IHHReduce; eauto.
    rewrite upd_label_overwrite in HType. by apply HType.
  - (* r_local *)
    apply Local_typing in HType.
    destruct HType as [ts [H1 [H2 H3]]]. subst.
    inversion H2. inversion H. subst.
    apply upd_label_unchanged_typing in H1.
    eapply IHHReduce => //=; eauto.
(* Qed. *) Admitted.

Lemma result_e_type: forall r ts s C,
    result_types_agree ts r ->
    e_typing s C (result_to_stack r) (Tf [::] ts).
Proof.
  move => r ts s C HResType.
  destruct r => //=; last by apply ety_trap.
  generalize dependent ts.
  induction l => //=; move => ts HResType; simpl in HResType.
  - destruct ts => //=.
    apply ety_a' => //=.
    by apply bet_empty.
  - destruct ts => //=.
    simpl in HResType.
    remove_bools_options.
    unfold types_agree in H.
    rewrite -cat1s.
    eapply et_composition' with (t2s := [:: v]); eauto => //=.
    + move/eqP in H. rewrite -H.
      apply const_typing' => //=; first by apply v_to_e_is_const.
      admit. (* prove or assert funci_agree if it's a funcref from result *)
    + remove_bools_options. subst.
      rewrite -cat1s -(cat1s _ ts).
      apply et_weakening_empty_1. apply IHl => //.
(* Qed. *) Admitted.

Lemma t_preservation_vs_type: forall s f es s' f' es' C C' lab ret t1s t2s hs hs',
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s f.(f_inst) C ->
    inst_typing s' f.(f_inst) C' ->
    e_typing s (upd_label (upd_local_label_return C (tc_local C ++ map typeof f.(f_locs)) (tc_label C) ret) lab) es (Tf t1s t2s) ->
    map typeof f.(f_locs) = map typeof f'.(f_locs).
Proof.
  move => s f es s' f' es' C C' lab ret t1s t2s hs hs' HReduce HST1 HST2 HIT1 HIT2 HType.
  generalize dependent t2s. generalize dependent t1s.
  generalize dependent lab.
  induction HReduce => //; move => lab t1s t2s HType.
  - invert_e_typing. convert_et_to_bet. invert_be_typing. simpl in *.
    replace (tc_local C) with ([::]: list value_type) in *;
        try (by symmetry; eapply inst_t_context_local_empty; eauto).
    rewrite H1. rewrite set_nth_map => //.
    rewrite set_nth_same_unchanged => //=.
  - assert (exists lab' t1s' t2s', e_typing s 
            (upd_label (upd_local_label_return C
              (tc_local C ++ map typeof f.(f_locs)) lab ret) lab')
            es (Tf t1s' t2s')).
    eapply lfilled_es_type_exists; eauto.
    destruct H1 as [lab' [t1s' [t2s' Het]]].
    by eapply IHHReduce; eauto.
Qed.

(* not tc_local since inst_typing fails so separate using upd_local *)
Lemma func_in_local_valid: forall s f j t v,
  lookup_N [seq typeof i | i <- f_locs f] j = Some t ->
  t = typeof v ->
  (forall f', (func_type_exists v s f')).
Admitted.
Lemma func_in_global_valid: forall s C i g v,
  lookup_N (tc_global C) i = Some g ->
  tg_t g = typeof v ->
  (forall f', (func_type_exists v s f')).
Admitted.
Lemma func_in_table_valid: forall s f C i a j ttype t tabv,
  lookup_N (tc_table C) i = Some ttype ->
  lookup_N (inst_tables (f_inst f)) i = Some a ->
  lookup_N (s_tables s) a = Some t ->
  lookup_N (tableinst_elem t) j = Some tabv ->
  tt_elem_type ttype = typeof_ref tabv ->
  (forall f', (func_type_exists (VAL_ref tabv) s f')).
Admitted.
Lemma func_in_elem_valid: forall s f C i j et elem v,
  lookup_N (tc_elem C) i = Some et ->
  selem s (f_inst f) i = Some elem ->
  lookup_N (eleminst_elem elem) j = Some v ->
  et = typeof_ref v ->
  (forall f', (func_type_exists (VAL_ref v) s f')).
Admitted.

Lemma t_preservation_e: forall s f es s' f' es' C t1s t2s lab ret hs hs',
    reduce hs s f es hs' s' f' es' ->
    store_typing s ->
    store_typing s' ->
    inst_typing s f.(f_inst) C ->
    inst_typing s' f.(f_inst) C ->
    e_typing s (upd_label (upd_local_label_return C (tc_local C ++ map typeof f.(f_locs)) (tc_label C) ret) lab) es (Tf t1s t2s) ->
    e_typing s' (upd_label (upd_local_label_return C (tc_local C ++ map typeof f'.(f_locs)) (tc_label C) ret) lab) es' (Tf t1s t2s).
Proof.
  move => s f es s' f' es' C t1s t2s lab ret hs hs' HReduce HST1 HST2.
  move: C ret lab t1s t2s.
  induction HReduce; move => C ret lab tx ty HIT1 HIT2 HType; subst;
  try eauto; try by apply ety_trap.
  - (* reduce_simple *)
    by eapply t_simple_preservation; eauto.

  - (* ref_func *)
    convert_et_to_bet.
    apply BI_ref_func_typing in HType.
    destruct HType as [tf [H1 [H2 H3]]].
    subst. apply et_weakening_empty_1.
    unfold lookup_N in H.
    eapply inst_typing_func in HIT1; eauto.
    destruct HIT1 as [cl HNthFunc].
    eapply ety_ref with (tf := cl_type cl).
    unfold funci_agree, option_map, lookup_N.
    by rewrite HNthFunc.

  - (* block *)
    apply const_list_get in H0. destruct H0. subst.
    split_et_composition.
    invert_e_typing.
    convert_et_to_bet.

    apply inst_typing_expand with (tb := tb) in HIT2.
    rewrite HIT2 in H.

    eapply Block_typing in H4; eauto.
    destruct H4 as [ts' [Ht1s [Ht2s H']]].
    simpl in H'. subst.
    repeat rewrite length_is_size in H2. rewrite v_to_e_size in H2.
    apply concat_cancel_last_n in Ht1s => //=;
      last by rewrite H2; apply size_map.
    remove_bools_options. subst.
    rewrite -(cats0 (ts ++ ts')) catA.
    apply ety_weakening.
    eapply ety_label; eauto;
      first by apply ety_a' => //; apply bet_weakening_empty_both;
        apply bet_empty.
    eapply et_composition' with (t2s := vs_to_vts x); eauto.
    apply const_list_typing' => //; last by apply v_to_e_is_const_list.
    apply ety_a'; first by apply to_e_list_basic.
    simpl. remember (to_e_list es) as bes. symmetry in Heqbes.
    apply b_e_elim in Heqbes. destruct Heqbes. subst. apply H'.
    
  - (* loop *)
    apply const_list_get in H0. destruct H0. subst.
    split_et_composition.
    invert_e_typing.
    convert_et_to_bet.

    apply inst_typing_expand with (tb := tb) in HIT2.
    rewrite HIT2 in H.

    eapply Loop_typing in H4; eauto.
    destruct H4 as [ts' [Ht1s [Ht2s H']]].
    simpl in H'. subst.
    repeat rewrite length_is_size in H2. rewrite v_to_e_size in H2.
    apply concat_cancel_last_n in Ht1s => //=;
      last by rewrite H2; apply size_map.
    remove_bools_options. subst.
    rewrite -(cats0 (ts ++ ts')) catA.
    apply ety_weakening.
    eapply ety_label with (ts := (vs_to_vts x)); eauto;
      last by repeat rewrite length_is_size size_map.
    apply ety_a'; first by auto_basic. apply bet_loop => //.
    eapply et_composition' with (t2s := vs_to_vts x); eauto.
    apply const_list_typing' => //; last by apply v_to_e_is_const_list.
    apply ety_a'; first by apply to_e_list_basic.
    simpl. remember (to_e_list es) as bes. symmetry in Heqbes.
    apply b_e_elim in Heqbes. destruct Heqbes. subst. apply H'.
    
  - (* if false *)
    apply const_list_get in H1. destruct H1. subst.
    split_et_composition.
    invert_e_typing.
    convert_et_to_bet.

    apply inst_typing_expand with (tb := tb) in HIT2.
    rewrite HIT2 in H.

    eapply If_typing in H5; eauto.
    destruct H5 as [ts' [Ht1s [Ht2s [Hes1 Hes2]]]].
    simpl in *. subst.
    repeat rewrite length_is_size in H3. rewrite v_to_e_size in H3.
    rewrite catA in Ht1s. apply concat_cancel_last in Ht1s => //=.
    destruct Ht1s. subst. rewrite catA in H1.
    apply concat_cancel_last_n in H1 => //=;
      last by rewrite H3; apply size_map.
    remove_bools_options. subst.
    rewrite -(cats0 (ts ++ ts0 ++ ts')).
    replace (ts ++ ts0 ++ ts' ++ t2s)
      with ((ts ++ ts0 ++ ts') ++ t2s);
      last by repeat rewrite catA.
    apply ety_weakening. simpl in *.
    eapply ety_label; eauto;
      first by apply ety_a' => //; apply bet_weakening_empty_both;
        apply bet_empty.
    eapply et_composition' with (t2s := (vs_to_vts x)); eauto.
    apply const_list_typing' => //; last by apply v_to_e_is_const_list.
    apply ety_a'; first by apply to_e_list_basic.
    simpl. remember (to_e_list es2) as bes. symmetry in Heqbes.
    apply b_e_elim in Heqbes. destruct Heqbes. subst. apply Hes2.

  - (* if true *)
    apply const_list_get in H1. destruct H1. subst.
    split_et_composition.
    invert_e_typing.
    convert_et_to_bet.

    apply inst_typing_expand with (tb := tb) in HIT2.
    rewrite HIT2 in H.

    eapply If_typing in H6; eauto.
    destruct H6 as [ts' [Ht1s [Ht2s [Hes1 Hes2]]]].
    simpl in *. subst.
    repeat rewrite length_is_size in H3. rewrite v_to_e_size in H3.
    rewrite catA in Ht1s. apply concat_cancel_last in Ht1s => //=.
    destruct Ht1s. subst. rewrite catA in H1.
    apply concat_cancel_last_n in H1 => //=;
      last by rewrite H3; apply size_map.
    remove_bools_options. subst.
    rewrite -(cats0 (ts ++ ts0 ++ ts')).
    replace (ts ++ ts0 ++ ts' ++ t2s)
      with ((ts ++ ts0 ++ ts') ++ t2s);
      last by repeat rewrite catA.
    apply ety_weakening. simpl in *.
    eapply ety_label; eauto;
      first by apply ety_a' => //; apply bet_weakening_empty_both;
        apply bet_empty.
    eapply et_composition' with (t2s := (vs_to_vts x)); eauto.
    apply const_list_typing' => //; last by apply v_to_e_is_const_list.
    apply ety_a'; first by apply to_e_list_basic.
    simpl. remember (to_e_list es1) as bes. symmetry in Heqbes.
    apply b_e_elim in Heqbes. destruct Heqbes. subst. apply Hes1.

  - (* Call *)
    convert_et_to_bet.
    apply Call_typing in HType.
    destruct HType as [ts [t1s' [t2s' [H1 [H2 H3]]]]].
    subst. simpl in H1.
    apply ety_weakening.
    eapply inst_typing_func in HIT1; eauto. destruct HIT1 as [cl HNthFunc].
    eapply ety_invoke; eauto.
    assert ((Tf t1s' t2s') = cl_type cl) as HFType; first by eapply tc_func_reference1; eauto.
    rewrite HFType.
    by eapply store_typed_cl_typed; eauto.
  - (* Call_indirect *)
    convert_et_to_bet.
    replace [::$VBN (VAL_int32 i); BI_call_indirect x y]
       with ([::$VBN (VAL_int32 i)] ++ [::BI_call_indirect x y]) in HType => //=.
    apply composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H1' [H2 [H3 H4]]]]]]].
    subst.
    invert_be_typing.
    apply Call_indirect_typing in H4.
    destruct H4 as [tn [tm [ts [H5 [H6 [H7 [H8 [H9 H10]]]]]]]].
    rewrite catA in H9. apply concat_cancel_last in H9. destruct H9. subst. 
    simpl in *.
    repeat apply ety_weakening.
    eapply ety_invoke; eauto.
    unfold stypes in H1.
    assert ((Tf tn tm) = cl_type cl) as HFType; first by eapply tc_func_reference2; eauto.
    rewrite HFType.
    by eapply store_typed_cl_typed; eauto.
  - (* Invoke native *)
    invert_e_typing.
    eapply Invoke_func_native_typing in H0; eauto.
    destruct H0 as [ts2 [C2 [H9 [H10 [H11 H12]]]]]. subst.
    apply concat_cancel_last_n in H9;
      last by (repeat rewrite length_is_size in H2; rewrite size_map).
    remove_bools_options. subst.
    simpl in *.
    apply ety_weakening. apply et_weakening_empty_1.
    assert (HCEmpty: tc_local C = [::]);
    first by eapply inst_t_context_local_empty; eauto.
    rewrite HCEmpty. simpl.
    apply ety_local => //.
    eapply mk_s_typing; eauto.
    eapply mk_frame_typing; eauto.
    assert (HC2Empty: tc_label C2 = [::]);
    first by eapply inst_t_context_label_empty; eauto.
    rewrite HC2Empty in H12.
    rewrite H8. rewrite map_cat => //=. rewrite n_zeros_typing.
    eapply ety_label with (ts := t2s) => //=.
    + apply ety_a'; auto_basic => //=.
      apply bet_weakening_empty_both. apply bet_empty.
    + apply ety_a'; auto_basic => //=; try by apply to_e_list_basic.
      remember (to_e_list es) as bes.
      assert (es_is_basic bes);
        first by rewrite Heqbes; apply bes_to_e_list_is_basic.
      replace (to_b_list bes) with (es);
        last by apply b_e_elim; by rewrite Heqbes.
      fold_upd_context. fold (vs_to_vts vcs).
      rewrite HC2Empty. apply H12.
  - (* Invoke host *)
    apply e_composition_typing in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H5' [H6 [H7 H8]]]]]]].
    subst.
    eapply Invoke_func_host_typing in H8; eauto.
    destruct H8 as [ts [H8 H9]]. subst.
    invert_e_typing.
    apply concat_cancel_last_n in H7;
      last by (repeat rewrite length_is_size in H3; rewrite size_map).
    remove_bools_options. subst.
    (* We require more knowledge of the host at this point. *)
    (* UPD: made it an axiom. *)
    assert (result_types_agree t2s r).
    {
      destruct host_instance. apply host_application_respect in H5 => //.
      unfold types_agree.
      clear.
      induction vcs => //=.
      by apply/andP => //=.
    }
    rewrite catA. apply et_weakening_empty_1.
    by apply result_e_type.

  - (* Get_local *)
    convert_et_to_bet.
    invert_be_typing. simpl in *.
    apply et_weakening_empty_1.
    assert (tc_local C = [::]);
      first by apply inst_t_context_local_empty in HIT1.
    rewrite H0 cat0s in H1.
    assert (t = typeof v). {
      assert (lookup_N (f_locs f) j <> None); first by rewrite H => //=.
      apply lookup_N_Some in H2.
      generalize dependent j.
      unfold lookup_N in *.
      induction (f_locs f) => //=; simpl in *.
      induction j => //=;
        first by intros H H1 _; inversion H; subst; inversion H1 => //=.
      intros.
      rewrite -cat1s in H. rewrite -cat1s in H1.
      replace ([::a] ++ l) with (([::a] ++ l)%list) in H => //.
      assert (List.nth_error (([:: typeof a] ++ [seq typeof i | i <- l])%list)
        (Pos.to_nat p) = Some t); first apply H1; clear H1; rename H3 into H1.
      rewrite List.nth_error_app2 in H; simpl; last by lias.
      rewrite List.nth_error_app2 in H1; simpl; last by lias.
      eapply IHl with (j := N.of_nat ((Pos.to_nat p) - 1));
      rewrite Nat2N.id => //=. lias.
    }
    rewrite H2. apply const_typing' => //=;
    first apply v_to_e_is_const.
    eapply func_in_local_valid; eauto.
    
  - (* Set_local *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    apply ety_a' => //. apply bet_weakening_empty_both. apply bet_empty.
    
  - (* Get_global *)
    convert_et_to_bet. invert_be_typing.
    apply et_weakening_empty_1. simpl in *.
    assert (t = typeof v); first by symmetry;
      eapply global_type_reference; eauto.
    rewrite H0. apply const_typing';
    first apply v_to_e_is_const.
    unfold option_map in H1. remove_bools_options.
    eapply func_in_global_valid; eauto.

    (* unfold option_map in H1.
    unfold sglob_val, option_map, sglob, sglob_ind in H.
    remove_bools_options. unfold func_type_exists.
    destruct (g_val g0) as [| |[]] => //=;
      try by (intro; exists (Tf [::] [::])). *)
    (* intro f1. unfold inst_typing, typing.inst_typing in HIT1. *)

  - (* Set_Global *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    apply ety_a' => //. apply bet_weakening_empty_both. apply bet_empty.

  - (* Table Get *)
    convert_et_to_bet. invert_be_typing.
    apply ety_weakening. apply et_weakening_empty_1.
    unfold stab_elem, stab in H. simpl in *.
    remove_bools_options.
    assert (tt_elem_type ttype = typeof_ref tabv).
      replace (ttype) with (tableinst_type t);
        last by eapply inst_typing_tab_ttype; eauto.
      eapply store_typing_tabv_type; eauto.
    rewrite H0.
    fold (typeof (VAL_ref tabv)). fold (v_to_e (VAL_ref tabv)).
    eapply const_ref_typing' => //=. destruct tabv => //.

    replace (List.nth_error (tableinst_elem t)
            (Z.to_nat (Wasm_int.Int32.unsigned i)))
       with (lookup_N (tableinst_elem t)
            (N.of_nat (Z.to_nat (Wasm_int.Int32.unsigned i)))) in H => //;
        last by unfold lookup_N; rewrite -> Nat2N.id.
    eapply func_in_table_valid; eauto.
    
  - (* Table Set *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    simpl in *. rewrite -(cat1s (T_num T_i32)) catA in H4.
    apply concat_cancel_last in H4.
    destruct H4. subst. rewrite catA in H1.
    apply concat_cancel_last in H1. destruct H1. subst.
    apply ety_a' => //. apply bet_weakening_empty_both. apply bet_empty.

  - (* Table Size *)
    convert_et_to_bet. invert_be_typing.
    apply et_weakening_empty_1. simpl in *.
    apply ety_a'; auto_basic. apply bet_const_num.

  - (* Table Grow Some *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    rewrite -(cat1s (T_ref (tt_elem_type ttype))) catA in H4.
    apply concat_cancel_last in H4.
    destruct H4. subst. rewrite catA in H0.
    apply concat_cancel_last in H0. destruct H0. subst.
    apply ety_a'; auto_basic. simpl. repeat apply bet_weakening.
    apply bet_weakening_empty_1. apply bet_const_num.
    
  - (* Table Grow None *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    rewrite -(cat1s (T_ref (tt_elem_type ttype))) catA in H4.
    apply concat_cancel_last in H4.
    destruct H4. subst. rewrite catA in H1.
    apply concat_cancel_last in H1. destruct H1. subst.
    apply ety_a'; auto_basic. simpl. repeat apply bet_weakening.
    apply bet_weakening_empty_1. apply bet_const_num.

  - (* Table Fill Return *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    rewrite -(cat1s (T_ref (tt_elem_type ttype)))
      (catA _ (T_num T_i32 :: [:: T_ref (tt_elem_type ttype)]) _) in H5.
    apply concat_cancel_last in H5. destruct H5. subst.
    rewrite -(cat1s (T_num T_i32)) in H2. repeat rewrite catA in H2.
    apply concat_cancel_last in H2. destruct H2. subst.
    rewrite catA in H1.
    apply concat_cancel_last in H1. destruct H1. subst.
    apply ety_a' => //. simpl. repeat apply bet_weakening.
    apply bet_weakening_empty_both. apply bet_empty.

  - (* Table Fill Step *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    rewrite -(cat1s (T_ref (tt_elem_type ttype)))
      (catA _ (T_num T_i32 :: [:: T_ref (tt_elem_type ttype)]) _) in H8.
    apply concat_cancel_last in H8. destruct H8. subst.
    rewrite -(cat1s (T_num T_i32)) in H5. repeat rewrite catA in H5.
    apply concat_cancel_last in H5. destruct H5. subst.
    rewrite catA in H4.
    apply concat_cancel_last in H4. destruct H4. subst.

    repeat apply ety_weakening.
    simpl in *. rewrite -cat1s.

    eapply et_composition'
      with (t2s := (t2s ++ [:: T_num T_i32])) => //=;
      first by apply ety_a'; auto_basic; repeat apply bet_weakening;
      apply bet_weakening_empty_1; apply bet_const_num.
    rewrite -cat1s.
    eapply et_composition'
      with (t2s := (t2s ++ [:: T_num T_i32] ++ [:: T_ref (typeof_ref tabv)])) => //=.
      rewrite -(cat1s _ [:: T_ref (typeof_ref tabv)]) catA.
      apply et_weakening_empty_1.
      fold (typeof (VAL_ref tabv)). fold (v_to_e (VAL_ref tabv)).
      eapply const_ref_typing' => //=. destruct tabv => //.
    rewrite -cat1s.
    eapply et_composition'
      with (t2s := t2s) => //=.
      apply ety_a'; auto_basic; repeat apply bet_weakening;
      apply bet_weakening_empty_2. simpl.
      eapply bet_table_set with (tabtype := ttype) => //=.
      by inversion H7.
    
    rewrite -cat1s.
    eapply et_composition'
      with (t2s := (t2s ++ [:: T_num T_i32])) => //=;
      first by apply ety_a'; auto_basic; repeat apply bet_weakening;
      apply bet_weakening_empty_1; apply bet_const_num.
    rewrite -cat1s.
    eapply et_composition'
      with (t2s := (t2s ++ [:: T_num T_i32] ++ [:: T_ref (typeof_ref tabv)])) => //=.
      rewrite -(cat1s _ [:: T_ref (typeof_ref tabv)]) catA.
      apply et_weakening_empty_1.
      fold (typeof (VAL_ref tabv)). fold (v_to_e (VAL_ref tabv)).
      eapply const_ref_typing' => //=. destruct tabv => //.
      simpl in *. rewrite -cat1s.
    eapply et_composition'
      with (t2s ++ [:: T_num T_i32; T_ref (typeof_ref tabv)] ++ [:: T_num T_i32]) => //=;
      first by replace ([:: T_num T_i32; T_ref (typeof_ref tabv); T_num T_i32])
         with ([:: T_num T_i32; T_ref (typeof_ref tabv)] ++ [:: T_num T_i32]) => //;
      rewrite -(cats0 [:: T_num T_i32; T_ref (typeof_ref tabv)]) => //;
      rewrite -catA cat0s; repeat apply ety_weakening;
      apply ety_a'; auto_basic; apply bet_const_num.
    apply ety_a'; auto_basic. apply bet_weakening_empty_2.
    eapply bet_table_fill with (tabtype := ttype) => //=.
    by inversion H7.

  - (* Table Copy Return *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    replace ([:: T_num T_i32; T_num T_i32; T_num T_i32])
       with ([:: T_num T_i32; T_num T_i32] ++ [:: T_num T_i32]) in H10 => //=.
    rewrite catA in H10.
    apply concat_cancel_last in H10. destruct H10. subst.
    rewrite -(cat1s (T_num T_i32)) in H4. repeat rewrite catA in H4.
    apply concat_cancel_last in H4. destruct H4. subst.
    rewrite catA in H3.
    apply concat_cancel_last in H3. destruct H3. subst.
    apply ety_a' => //. simpl. repeat apply bet_weakening.
    apply bet_weakening_empty_both. apply bet_empty.

  - (* Table Copy Forward *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    replace ([:: T_num T_i32; T_num T_i32; T_num T_i32])
      with ([:: T_num T_i32; T_num T_i32] ++ [:: T_num T_i32]) in H15 => //=.
    rewrite catA in H15.
    apply concat_cancel_last in H15. destruct H15. subst.
    rewrite -(cat1s (T_num T_i32)) in H9. repeat rewrite catA in H9.
    apply concat_cancel_last in H9. destruct H9. subst.
    rewrite catA in H8.
    apply concat_cancel_last in H8. destruct H8. subst.
    apply ety_a' => //;
      first by unfold es_is_basic, e_is_basic;
      repeat apply List.Forall_cons; eauto.
    simpl. repeat apply bet_weakening.
    apply bet_weakening_empty_both.

    simpl in *. rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32]);
      first by apply bet_const_num.
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32] ++ [:: T_num T_i32]);
      first by apply bet_weakening_empty_1; apply bet_const_num.
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32] ++ [:: T_ref (tt_elem_type t)]);
      first by apply bet_weakening; eapply bet_table_get with (tabtype := t).
    simpl in *. rewrite -cat1s.
    eapply bet_composition' with (t2s := [::]);
      first by eapply bet_table_set with (tabtype := ttype).
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32]);
      first by apply bet_const_num.
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32] ++ [:: T_num T_i32]);
      first by apply bet_weakening_empty_1; apply bet_const_num.
    simpl in *. rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32; T_num T_i32] ++ [:: T_num T_i32]);
      first by apply bet_weakening_empty_1; apply bet_const_num.
    by eapply bet_table_copy with (tabtype1 := ttype) (tabtype2 := t).

  - (* Table Copy Backward *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    replace ([:: T_num T_i32; T_num T_i32; T_num T_i32])
      with ([:: T_num T_i32; T_num T_i32] ++ [:: T_num T_i32]) in H15 => //=.
    rewrite catA in H15.
    apply concat_cancel_last in H15. destruct H15. subst.
    rewrite -(cat1s (T_num T_i32)) in H9. repeat rewrite catA in H9.
    apply concat_cancel_last in H9. destruct H9. subst.
    rewrite catA in H8.
    apply concat_cancel_last in H8. destruct H8. subst.
    apply ety_a' => //;
      first by unfold es_is_basic, e_is_basic;
      repeat apply List.Forall_cons; eauto.
    simpl. repeat apply bet_weakening.
    apply bet_weakening_empty_both.

    simpl in *. rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32]);
      first by apply bet_const_num.
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32] ++ [:: T_num T_i32]);
      first by apply bet_weakening_empty_1; apply bet_const_num.
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32] ++ [:: T_ref (tt_elem_type t)]);
      first by apply bet_weakening; eapply bet_table_get with (tabtype := t).
    simpl in *. rewrite -cat1s.
    eapply bet_composition' with (t2s := [::]);
      first by eapply bet_table_set with (tabtype := ttype).
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32]);
      first by apply bet_const_num.
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32] ++ [:: T_num T_i32]);
      first by apply bet_weakening_empty_1; apply bet_const_num.
    simpl in *. rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32; T_num T_i32] ++ [:: T_num T_i32]);
      first by apply bet_weakening_empty_1; apply bet_const_num.
    by eapply bet_table_copy with (tabtype1 := ttype) (tabtype2 := t).
    
  - (* Table Init Return *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    replace ([:: T_num T_i32; T_num T_i32; T_num T_i32])
      with ([:: T_num T_i32; T_num T_i32] ++ [:: T_num T_i32]) in H9 => //=.
    rewrite catA in H9.
    apply concat_cancel_last in H9. destruct H9. subst.
    rewrite -(cat1s (T_num T_i32)) in H4. repeat rewrite catA in H4.
    apply concat_cancel_last in H4. destruct H4. subst.
    rewrite catA in H3.
    apply concat_cancel_last in H3. destruct H3. subst.
    apply ety_a' => //. simpl. repeat apply bet_weakening.
    apply bet_weakening_empty_both. apply bet_empty.

  - (* Table Init Step *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    replace ([:: T_num T_i32; T_num T_i32; T_num T_i32])
      with ([:: T_num T_i32; T_num T_i32] ++ [:: T_num T_i32]) in H14 => //=.
    rewrite catA in H14.
    apply concat_cancel_last in H14. destruct H14. subst.
    rewrite -(cat1s (T_num T_i32)) in H9. repeat rewrite catA in H9.
    apply concat_cancel_last in H9. destruct H9. subst.
    rewrite catA in H8.
    apply concat_cancel_last in H8. destruct H8. subst.

    simpl in *. rewrite -cat1s.
    repeat apply ety_weakening.

    eapply et_composition'
      with (t2s := (t2s ++ [:: T_num T_i32])) => //=;
      first by apply ety_a'; auto_basic; repeat apply bet_weakening;
      apply bet_weakening_empty_1; apply bet_const_num.
    rewrite -cat1s.
    eapply et_composition'
      with (t2s := (t2s ++ [:: T_num T_i32] ++ [:: T_ref (typeof_ref v)])) => //=.
      rewrite -(cat1s _ [:: T_ref (typeof_ref v)]) catA.
      apply et_weakening_empty_1.
      fold (typeof (VAL_ref v)). fold (v_to_e (VAL_ref v)).
      eapply const_ref_typing' => //=. destruct v => //.

    eapply func_in_elem_valid; eauto.
    unfold selem in H0. remove_bools_options.
    eapply inst_typing_elemv_type; eauto.

    rewrite -cat1s.
    eapply et_composition' with (t2s := t2s) => //=.
    {
      apply ety_a'; auto_basic; repeat apply bet_weakening;
      apply bet_weakening_empty_2. simpl.
      eapply bet_table_set with (tabtype := ttype) => //=.
      
      unfold stab in H.
      unfold selem in H0.
      remove_bools_options.
      unfold lookup_N in *.
      eapply inst_typing_elemv_type; eauto.
    }
    
    rewrite -cat1s.
    eapply et_composition'
      with (t2s := (t2s ++ [:: T_num T_i32])) => //=;
      first by apply ety_a'; auto_basic; repeat apply bet_weakening;
      apply bet_weakening_empty_1; apply bet_const_num.
    rewrite -cat1s.
    eapply et_composition'
      with (t2s := (t2s ++ [:: T_num T_i32] ++ [:: T_num T_i32])) => //=;
      first by apply ety_a'; auto_basic; repeat apply bet_weakening;
      rewrite -(cat1s (T_num T_i32) [:: T_num T_i32]);
      apply bet_weakening_empty_1; apply bet_const_num.
    rewrite -cat1s.
    eapply et_composition'
      with (t2s := (t2s ++ [:: T_num T_i32] ++ [:: T_num T_i32]++ [:: T_num T_i32])) => //=;
      first by apply ety_a'; auto_basic; repeat apply bet_weakening;
      repeat rewrite -(cat1s (T_num T_i32) [:: T_num T_i32; T_num T_i32]);
      repeat rewrite -(cat1s (T_num T_i32) [:: T_num T_i32]);
      repeat apply bet_weakening;
      apply bet_weakening_empty_1; apply bet_const_num.
    apply ety_a'; auto_basic; simpl. apply bet_weakening_empty_2.
    eapply bet_table_init with (tabtype := ttype) => //=.

  - (* Elem Drop *)
    convert_et_to_bet. invert_be_typing. apply ety_a' => //.
    apply bet_weakening_empty_both. apply bet_empty.

  - (* Load None *)
    convert_et_to_bet. invert_be_typing.
    rewrite catA.
    apply et_weakening_empty_1.
    apply ety_a'; auto_basic.
    destruct t => //=; apply bet_const_num.

  - (* Load Some *)
    convert_et_to_bet. invert_be_typing.
    rewrite catA.
    apply et_weakening_empty_1.
    apply ety_a'; auto_basic.
    destruct t => //=; apply bet_const_num.
    
  - (* Store None *)
    convert_et_to_bet. invert_be_typing.
    apply ety_weakening.
    rewrite -(cat1s (T_num T_i32)) catA in H4.
    apply concat_cancel_last in H4. destruct H4. subst.
    rewrite catA in H3.
    apply concat_cancel_last in H3. destruct H3. subst.
    apply ety_a' => //. simpl.
    apply bet_weakening_empty_both. apply bet_empty.
    
  - (* Store Some *)
    convert_et_to_bet. invert_be_typing.
    apply ety_weakening.
    rewrite -(cat1s (T_num T_i32)) catA in H4.
    apply concat_cancel_last in H4. destruct H4. subst.
    rewrite catA in H3.
    apply concat_cancel_last in H3. destruct H3. subst.
    apply ety_a' => //. simpl.
    apply bet_weakening_empty_both. apply bet_empty.

  - (* Current_memory *)
    convert_et_to_bet. invert_be_typing.
    apply ety_a'; auto_basic.
    apply bet_weakening_empty_1.
    by apply bet_const_num.

  - (* Grow_memory success *)
    convert_et_to_bet. invert_be_typing.
    apply ety_a'; auto_basic. rewrite catA.
    apply bet_weakening_empty_1.
    destruct (mem_size m) => //=;
    apply bet_const_num.

  - (* Grow_memory fail *)
    convert_et_to_bet. invert_be_typing.
    apply ety_a'; auto_basic. rewrite catA.
    apply bet_weakening_empty_1. simpl.
    by apply bet_const_num.

  - (* Memory Fill Return *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    replace ([:: T_num T_i32; T_num T_i32; T_num T_i32])
      with ([:: T_num T_i32; T_num T_i32] ++ [:: T_num T_i32]) in H4 => //=.
    rewrite catA in H4.
    apply concat_cancel_last in H4. destruct H4. subst.
    rewrite -(cat1s (T_num T_i32)) in H2. repeat rewrite catA in H2.
    apply concat_cancel_last in H2. destruct H2. subst.
    rewrite catA in H1.
    apply concat_cancel_last in H1. destruct H1. subst.
    apply ety_a' => //. simpl. repeat apply bet_weakening.
    apply bet_weakening_empty_both. apply bet_empty.

  - (* Memory Fill Step *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    replace ([:: T_num T_i32; T_num T_i32; T_num T_i32])
      with ([:: T_num T_i32; T_num T_i32] ++ [:: T_num T_i32]) in H7 => //=.
    rewrite catA in H7.
    apply concat_cancel_last in H7. destruct H7. subst.
    rewrite -(cat1s (T_num T_i32)) in H5. repeat rewrite catA in H5.
    apply concat_cancel_last in H5. destruct H5. subst.
    rewrite catA in H4.
    apply concat_cancel_last in H4. destruct H4. subst.

    apply ety_a' => //;
      first by unfold es_is_basic, e_is_basic;
      repeat apply List.Forall_cons; eauto.
    simpl. repeat apply bet_weakening.
    apply bet_weakening_empty_both.

    simpl in *. rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32]);
      first by apply bet_const_num.
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32] ++ [:: T_num T_i32]);
      first by apply bet_weakening_empty_1; apply bet_const_num.
    simpl in *. rewrite -cat1s.
    eapply bet_composition' with (t2s := [::]);
      first by apply bet_store.
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32]);
      first by apply bet_const_num.
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32] ++ [:: T_num T_i32]);
      first by apply bet_weakening_empty_1; apply bet_const_num.
    simpl in *. rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32; T_num T_i32] ++ [:: T_num T_i32]);
      first by apply bet_weakening_empty_1; apply bet_const_num.
    simpl in *. rewrite -cat1s.
    simpl in *. apply bet_memory_fill => //=.
    
  - (* Memory Copy Return *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    replace ([:: T_num T_i32; T_num T_i32; T_num T_i32])
      with ([:: T_num T_i32; T_num T_i32] ++ [:: T_num T_i32]) in H5 => //=.
    rewrite catA in H5.
    apply concat_cancel_last in H5. destruct H5. subst.
    rewrite -(cat1s (T_num T_i32)) in H3. repeat rewrite catA in H3.
    apply concat_cancel_last in H3. destruct H3. subst.
    rewrite catA in H2.
    apply concat_cancel_last in H2. destruct H2. subst.
    apply ety_a' => //. simpl. repeat apply bet_weakening.
    apply bet_weakening_empty_both. apply bet_empty.

  - (* Memory Copy Forward *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    replace ([:: T_num T_i32; T_num T_i32; T_num T_i32])
      with ([:: T_num T_i32; T_num T_i32] ++ [:: T_num T_i32]) in H10 => //=.
    rewrite catA in H10.
    apply concat_cancel_last in H10. destruct H10. subst.
    rewrite -(cat1s (T_num T_i32)) in H8. repeat rewrite catA in H8.
    apply concat_cancel_last in H8. destruct H8. subst.
    rewrite catA in H7.
    apply concat_cancel_last in H7. destruct H7. subst.
    apply ety_a' => //;
      first by unfold es_is_basic, e_is_basic;
      repeat apply List.Forall_cons; eauto.
    simpl. repeat apply bet_weakening.
    apply bet_weakening_empty_both.

    simpl in *. rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32]);
      first by apply bet_const_num.
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32] ++ [:: T_num T_i32]);
      first by apply bet_weakening_empty_1; apply bet_const_num.
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32] ++ [:: T_num T_i32]);
      first by apply bet_weakening; apply bet_load.
    simpl in *. rewrite -cat1s.
    eapply bet_composition' with (t2s := [::]);
      first by apply bet_store.
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32]);
      first by apply bet_const_num.
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32] ++ [:: T_num T_i32]);
      first by apply bet_weakening_empty_1; apply bet_const_num.
    simpl in *. rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32; T_num T_i32] ++ [:: T_num T_i32]);
      first by apply bet_weakening_empty_1; apply bet_const_num.
    simpl in *. apply bet_memory_copy => //=.

  - (* Memory Copy Backward *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    replace ([:: T_num T_i32; T_num T_i32; T_num T_i32])
      with ([:: T_num T_i32; T_num T_i32] ++ [:: T_num T_i32]) in H10 => //=.
    rewrite catA in H10.
    apply concat_cancel_last in H10. destruct H10. subst.
    rewrite -(cat1s (T_num T_i32)) in H8. repeat rewrite catA in H8.
    apply concat_cancel_last in H8. destruct H8. subst.
    rewrite catA in H7.
    apply concat_cancel_last in H7. destruct H7. subst.
    apply ety_a' => //;
      first by unfold es_is_basic, e_is_basic;
      repeat apply List.Forall_cons; eauto.
    simpl. repeat apply bet_weakening.
    apply bet_weakening_empty_both.

    simpl in *. rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32]);
      first by apply bet_const_num.
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32] ++ [:: T_num T_i32]);
      first by apply bet_weakening_empty_1; apply bet_const_num.
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32] ++ [:: T_num T_i32]);
      first by apply bet_weakening; apply bet_load.
    simpl in *. rewrite -cat1s.
    eapply bet_composition' with (t2s := [::]);
      first by apply bet_store.
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32]);
      first by apply bet_const_num.
    rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32] ++ [:: T_num T_i32]);
      first by apply bet_weakening_empty_1; apply bet_const_num.
    simpl in *. rewrite -cat1s.
    eapply bet_composition' with (t2s := [:: T_num T_i32; T_num T_i32] ++ [:: T_num T_i32]);
      first by apply bet_weakening_empty_1; apply bet_const_num.
    simpl in *. apply bet_memory_copy => //=.

  - (* Memory Init Return *)
  invert_e_typing. convert_et_to_bet. invert_be_typing.
  replace ([:: T_num T_i32; T_num T_i32; T_num T_i32])
    with ([:: T_num T_i32; T_num T_i32] ++ [:: T_num T_i32]) in H7 => //=.
  rewrite catA in H7.
  apply concat_cancel_last in H7. destruct H7. subst.
  rewrite -(cat1s (T_num T_i32)) in H4. repeat rewrite catA in H4.
  apply concat_cancel_last in H4. destruct H4. subst.
  rewrite catA in H3.
  apply concat_cancel_last in H3. destruct H3. subst.
  apply ety_a' => //. apply bet_weakening_empty_both. apply bet_empty.

  - (* Memory Init Step *)
  invert_e_typing. convert_et_to_bet. invert_be_typing.
  replace ([:: T_num T_i32; T_num T_i32; T_num T_i32])
    with ([:: T_num T_i32; T_num T_i32] ++ [:: T_num T_i32]) in H12 => //=.
  rewrite catA in H12.
  apply concat_cancel_last in H12. destruct H12. subst.
  rewrite -(cat1s (T_num T_i32)) in H9. repeat rewrite catA in H9.
  apply concat_cancel_last in H9. destruct H9. subst.
  rewrite catA in H8.
  apply concat_cancel_last in H8. destruct H8. subst.

  simpl in *. rewrite -cat1s.
  repeat apply ety_weakening.

  eapply et_composition'
    with (t2s := (t2s ++ [:: T_num T_i32])) => //=;
    first by apply ety_a'; auto_basic; repeat apply bet_weakening;
    apply bet_weakening_empty_1; apply bet_const_num.
  rewrite -cat1s.
  eapply et_composition'
    with (t2s := (t2s ++ [:: T_num T_i32] ++ [:: T_num T_i32])) => //=;
    first by apply ety_a'; auto_basic; repeat apply bet_weakening;
    rewrite -(cat1s (T_num T_i32) [:: T_num T_i32]);
    apply bet_weakening_empty_1; apply bet_const_num.
  rewrite -cat1s.
  eapply et_composition'
    with (t2s := t2s) => //=.
    apply ety_a'; auto_basic; repeat apply bet_weakening;
    apply bet_weakening_empty_2. simpl.
    eapply bet_store => //=.
  
  rewrite -cat1s.
  eapply et_composition'
    with (t2s := (t2s ++ [:: T_num T_i32])) => //=;
    first by apply ety_a'; auto_basic; repeat apply bet_weakening;
    apply bet_weakening_empty_1; apply bet_const_num.
  rewrite -cat1s.
  eapply et_composition'
    with (t2s := (t2s ++ [:: T_num T_i32] ++ [:: T_num T_i32])) => //=;
    first by apply ety_a'; auto_basic; repeat apply bet_weakening;
    rewrite -(cat1s (T_num T_i32) [:: T_num T_i32]);
    apply bet_weakening_empty_1; apply bet_const_num.
  rewrite -cat1s.
  eapply et_composition'
    with (t2s := (t2s ++ [:: T_num T_i32] ++ [:: T_num T_i32]++ [:: T_num T_i32])) => //=;
    first by apply ety_a'; auto_basic; repeat apply bet_weakening;
    repeat rewrite -(cat1s (T_num T_i32) [:: T_num T_i32; T_num T_i32]);
    repeat rewrite -(cat1s (T_num T_i32) [:: T_num T_i32]);
    repeat apply bet_weakening;
    apply bet_weakening_empty_1; apply bet_const_num.
  apply ety_a'; auto_basic; simpl. apply bet_weakening_empty_2.
  eapply bet_memory_init => //=.

  - (* Data Drop *)
    invert_e_typing. convert_et_to_bet. invert_be_typing.
    apply ety_a' => //. apply bet_weakening_empty_both.
    apply bet_empty.
    
  (* From the structure, it seems that some form of induction
      is required to prove these 2 cases. *)

  - (* r_label *)
    generalize dependent les. generalize dependent les'.
    generalize dependent ty. generalize dependent tx.
    generalize dependent lab. generalize dependent ret.
    induction k; dependent destruction lh;
    move => ret lab tx ty les' HLF' les HLF HType;
    unfold lfilled in HLF', HLF; move/eqP in HLF'; move/eqP in HLF;
    simpl in HLF', HLF; subst.
    (* LH_base *)
    + invert_e_typing.
      eapply et_composition'.
      -- instantiate (1 := ts ++ ts0 ++ t1s0).
        rewrite -H1 catA. apply et_weakening_empty_1.
        assert (typing.e_typing s (upd_label (upd_local_label_return C
                  (tc_local C ++ [seq typeof i | i <- f_locs f']) 
                  (tc_label C) ret) lab) (v_to_e_list l)
                (Tf [::] (vs_to_vts l))); first by
          apply const_list_typing' => //=; first by apply v_to_e_is_const_list.
        eapply store_extension_e_typing; try apply HST1 => //; try by [].
        eapply store_extension_reduce; eauto.
      -- eapply et_composition'; eauto.
         ++ instantiate (1 := ts ++ ts0 ++ t3s).
            repeat apply ety_weakening.
            by eapply IHHReduce; eauto => //.
         ++ repeat apply ety_weakening.
            assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
            rewrite HCEmpty in H0. rewrite HCEmpty.
            replace (map typeof f'.(f_locs)) with (map typeof f.(f_locs)) => //;
              last by eapply t_preservation_vs_type; eauto.
            eapply store_extension_e_typing; try apply HST1 => //; try by [].
            eapply store_extension_reduce with (es := es); eauto.
            
    (* LH_rec *)
    + rewrite -cat1s in HType. invert_e_typing.
      eapply et_composition'.
      -- instantiate (1 := ts ++ ts0 ++ t1s0).
        simpl in H5. rewrite upd_label_overwrite in H5.
        eapply lfilled_es_type_exists with (lh := lh) (es := es) in H5;
          eauto; last by unfold lfilled.
        destruct H5 as [lab' [t1s' [t2s' H5]]].
        rewrite -H1 catA. apply et_weakening_empty_1.
        assert (typing.e_typing s (upd_label (upd_local_label_return C
                  (tc_local C ++ [seq typeof i | i <- f_locs f']) 
                  (tc_label C) ret) lab) (v_to_e_list l)
                (Tf [::] (vs_to_vts l))); first by
          apply const_list_typing' => //=; first by apply v_to_e_is_const_list.
        eapply store_extension_e_typing; try apply HST1 => //; try by [].
        eapply store_extension_reduce; eauto. apply H5.
      -- rewrite -cat1s. eapply et_composition'; eauto.
         ++ instantiate (1 := ts ++ ts0 ++ t1s0 ++ t1s1).
            repeat apply ety_weakening.
            apply et_weakening_empty_1.
            eapply ety_label; eauto.
            * assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
              rewrite HCEmpty in H4. rewrite HCEmpty.
              simpl in H5. rewrite upd_label_overwrite in H5.
              eapply lfilled_es_type_exists with (lh := lh) (es := es) in H5;
                eauto; last by unfold lfilled.
              destruct H5 as [lab' [t1s' [t2s' H5]]].
              rewrite upd_label_overwrite in H5.
              replace (map typeof f'.(f_locs)) with (map typeof f.(f_locs)) => //;
                last by eapply t_preservation_vs_type; eauto.
              eapply store_extension_e_typing; try apply HST1 => //; try by [].
              eapply store_extension_reduce; eauto.
            * simpl in *. unfold lfilled in IHk.
              eapply IHk; eauto.
         ++ repeat apply ety_weakening.
            assert (HCEmpty: tc_local C = [::]); first by eapply inst_t_context_local_empty; eauto.
            rewrite HCEmpty in H0. rewrite HCEmpty.
            simpl in H5. rewrite upd_label_overwrite in H5.
            eapply lfilled_es_type_exists with (lh := lh) (es := es) in H5;
              eauto; last by unfold lfilled.
            destruct H5 as [lab' [t1s' [t2s' H5]]].
            rewrite upd_label_overwrite in H5.
            replace (map typeof f'.(f_locs)) with (map typeof f.(f_locs)) => //;
              last by eapply t_preservation_vs_type; eauto.
            eapply store_extension_e_typing; try apply HST1 => //; try by [].
            eapply store_extension_reduce; eauto.
  - (* r_local *)
    apply Local_typing in HType.
    destruct HType as [ts [H1 [H2 H3]]]. subst.
    apply et_weakening_empty_1.
    apply ety_local => //.
    inversion H2. inversion H. subst.
    apply upd_label_unchanged_typing in H1.
    eapply mk_s_typing; eauto.
    + eapply mk_frame_typing => //.
      eapply inst_typing_extension; eauto.
      eapply store_extension_reduce; eauto.
      replace (f_inst f') with (f_inst f); eauto;
        first by eapply reduce_inst_unchanged; eauto.
    + fold_upd_context.
      eapply IHHReduce; eauto.
      eapply inst_typing_extension; eauto.
      eapply store_extension_reduce; eauto.
Qed.
  
Theorem t_preservation: forall s f es s' f' es' ts hs hs',
    reduce hs s f es hs' s' f' es' ->
    config_typing s f es ts ->
    config_typing s' f' es' ts.
Proof.
  move => s f es s' f' es' ts hs hs' HReduce HType.
  inversion HType. inversion H0. inversion H5. subst.
  assert (store_extension s s' /\ store_typing s').
  { apply upd_label_unchanged_typing in H7.
    by eapply store_extension_reduce; eauto. }
  destruct H1.
  assert (inst_typing s' (f_inst f) C1);
    first by eapply inst_typing_extension; eauto.
  apply mk_config_typing; eauto.
  eapply mk_s_typing; eauto.
  eapply mk_frame_typing; eauto.
  replace (f_inst f') with (f_inst f); eauto;
    first by eapply reduce_inst_unchanged; eauto.
  fold_upd_context.
  by eapply t_preservation_e; eauto.
Qed.

End Host.
