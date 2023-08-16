(** Miscellaneous properties about Wasm operations **)
(* (C) Rao Xiaojia, M. Bodin - see LICENSE.txt *)

From Wasm Require Export datatypes_properties operations typing opsem common.
From mathcomp Require Import ssreflect ssrfun ssrnat ssrbool eqtype seq.
From StrongInduction Require Import StrongInduction.
From Coq Require Import Bool Program.Equality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * Basic Lemmas **)

Lemma const_list_concat: forall vs1 vs2,
    const_list vs1 ->
    const_list vs2 ->
    const_list (vs1 ++ vs2).
Proof.
  move => vs1 vs2. elim vs1 => {vs1} //=.
  - move => a vs1' IHvs1 H1 H2. simpl in H1. simpl.
    apply andb_true_iff in H1. destruct H1. rewrite IHvs1 //=. by rewrite andbT.
Qed.
Lemma basic_const_list_concat: forall vs1 vs2,
    basic_const_list vs1 ->
    basic_const_list vs2 ->
    basic_const_list (vs1 ++ vs2).
Proof.
  move => vs1 vs2. elim vs1 => {vs1} //=.
  - move => a vs1' IHvs1 H1 H2. simpl in H1. simpl.
    apply andb_true_iff in H1. destruct H1. rewrite IHvs1 //=. by rewrite andbT.
Qed.

Lemma const_list_split: forall vs1 vs2,
    const_list (vs1 ++ vs2) ->
    const_list vs1 /\
    const_list vs2.
Proof.
  induction vs1 => //=; move => vs2 HConst.
  move/andP in HConst. destruct HConst.
  apply IHvs1 in H0. destruct H0.
  split => //.
  by apply/andP.
Qed.
Lemma basic_const_list_split: forall vs1 vs2,
    basic_const_list (vs1 ++ vs2) ->
    basic_const_list vs1 /\
    basic_const_list vs2.
Proof.
  induction vs1 => //=; move => vs2 HConst.
  move/andP in HConst. destruct HConst.
  apply IHvs1 in H0. destruct H0.
  split => //.
  by apply/andP.
Qed.   

(** This lemma justifies the computation “to the first non-[const_list]”. **)
Lemma const_list_concat_inv : forall vs1 vs2 e1 e2 es1 es2,
    const_list vs1 ->
    const_list vs2 ->
    ~ is_const e1 ->
    ~ is_const e2 ->
    vs1 ++ e1 :: es1 = vs2 ++ e2 :: es2 ->
    vs1 = vs2 /\ e1 = e2 /\ es1 = es2.
Proof.
  induction vs1 => vs2 e1 e2 es1 es2 C1 C2 N1 N2; destruct vs2 => /=; inversion 1; subst;
    try move: C1 => /= /andP [? ?] //;
    try move: C2 => /= /andP [? ?] //.
  - done.
  - apply IHvs1 in H2 => //. move: H2 => [? [? ?]]. by subst.
Qed.
Lemma basic_const_list_concat_inv : forall vs1 vs2 e1 e2 es1 es2,
    basic_const_list vs1 ->
    basic_const_list vs2 ->
    ~ is_basic_const e1 ->
    ~ is_basic_const e2 ->
    vs1 ++ e1 :: es1 = vs2 ++ e2 :: es2 ->
    vs1 = vs2 /\ e1 = e2 /\ es1 = es2.
Proof.
  induction vs1 => vs2 e1 e2 es1 es2 C1 C2 N1 N2; destruct vs2 => /=; inversion 1; subst;
    try move: C1 => /= /andP [? ?] //;
    try move: C2 => /= /andP [? ?] //.
  - done.
  - apply IHvs1 in H2 => //. move: H2 => [? [? ?]]. by subst.
Qed.

Lemma const_list_take: forall vs l,
    const_list vs ->
    const_list (take l vs).
Proof.
  move => vs. induction vs => //=.
  - move => l HConst. destruct l => //=.
    + simpl. simpl in HConst. apply andb_true_iff in HConst. destruct HConst.
      apply andb_true_iff. split => //. by apply IHvs.
Qed.
Lemma basic_const_list_take: forall vs l,
    basic_const_list vs ->
    basic_const_list (take l vs).
Proof.
  move => vs. induction vs => //=.
  - move => l HConst. destruct l => //=.
    + simpl. simpl in HConst. apply andb_true_iff in HConst. destruct HConst.
      apply andb_true_iff. split => //. by apply IHvs.
Qed.

Lemma v_to_e_is_const: forall v,
    is_const (v_to_e v).
Proof.
  destruct v as [ | | ref] => //; last by destruct ref.
Qed.

Lemma v_to_e_to_v: forall v e,
    v_to_e v = e <->
    e_to_v e = Some v.
Proof.
  move => v e.
  split; move => H.
  - destruct v as [ | | ref]; subst => //=; last by destruct ref.
  - destruct e; simpl in H; subst; try by inversion H => //=.
    destruct b; simpl in H; inversion H; by subst => //=.
Qed.
Lemma v_to_be_to_v: forall v e,
    is_basic_const (v_to_e v) /\ v_to_be v = e
    <-> be_to_v e = Some v.
Proof.
  move => v e.
  split; move => H.
  - destruct v as [ | | []] => //=;
    unfold is_basic_const in H; simpl in H;
      destruct H => //=; subst => //=.
  - destruct e; simpl in H; subst; inversion H => //=;
    split => //=; unfold is_basic_const => //=.
Qed.

Lemma v_to_e_is_const_list: forall vs,
    const_list (v_to_e_list vs).
Proof.
  move => vs. elim: vs => //=.
  intros; apply/andP; split => //.
  by apply v_to_e_is_const.
Qed.

Lemma v_to_e_cat: forall vs1 vs2,
    v_to_e_list vs1 ++ v_to_e_list vs2 = v_to_e_list (vs1 ++ vs2).
Proof.
  intros. unfold v_to_e_list.
  by rewrite map_cat.
Qed.
Lemma v_to_be_cat: forall vs1 vs2,
    v_to_be_list vs1 ++ v_to_be_list vs2 = v_to_be_list (vs1 ++ vs2).
Proof.
  intros. unfold v_to_be_list.
  by rewrite map_cat.
Qed.

Lemma split_vals_e_v_to_e_duality: forall es vs es',
    split_vals_e es = (vs, es') ->
    es = (v_to_e_list vs) ++ es'.
Proof.
  move => es. elim: es => //=.
  - move => vs es'; by inversion 1.
  - move => a l H es es' HSplit.
    destruct (split_vals_e l) as [lvs les] eqn:Hlves.
    destruct (e_to_v a) as [v | ] eqn:Hetov => //=.
    + inversion HSplit; subst; clear HSplit => /=.
      apply v_to_e_to_v in Hetov; subst.
      f_equal.
      by apply H.
    + by inversion HSplit.
Qed.

Lemma is_basic_const_alt: forall a,
  is_basic_const a <-> e_is_basic a /\ is_const a.
Proof.
  split; intros.
  - unfold is_basic_const in H. split;
    destruct a => //=; destruct b => //=;
    unfold e_is_basic; eauto.
  - destruct H. unfold is_basic_const.
    destruct a => //=; [destruct b => //= | |];
    unfold e_is_basic in H; destruct H; discriminate.
Qed.
Lemma basic_const_list_alt: forall a,
  basic_const_list a <-> es_is_basic a /\ const_list a.
Proof.
  split; intros.
  - unfold basic_const_list in H. induction a; split => //=;
    unfold List.forallb in H; move/andP in H; destruct H;
    fold (List.forallb is_basic_const a0) in H0.
    + unfold es_is_basic. apply List.Forall_cons => //=.
      * destruct a => //=. by exists b.
      * apply IHa in H0. destruct H0 => //=.
    + apply/andP. split.
      * apply is_basic_const_alt in H. destruct H => //=.
      * apply IHa in H0. destruct H0 => //=.
  - destruct H. unfold basic_const_list.
    induction a => //=. apply/andP. split;
    unfold es_is_basic in H; unfold const_list in H0;
    unfold List.forallb in H0; move/andP in H0; destruct H0;
    fold (List.forallb is_const a0) in H1.
    + apply List.Forall_inv in H.
      apply is_basic_const_alt. split => //=.
    + apply List.Forall_inv_tail in H.
      fold (List.forallb is_const a0) in H1. apply IHa => //=.
Qed.

Lemma const_list_cons : forall a l,
  const_list (a :: l) = is_const a && const_list l.
Proof. by []. Qed.
Lemma basic_const_list_cons : forall a l,
  is_const a ->
  e_is_basic a ->
  basic_const_list l ->
  basic_const_list (a :: l).
Proof.
  intros a l H1 H2 H3.
  unfold basic_const_list.
  rewrite <- cat1s.
  replace ([::a] ++ l) with (([::a] ++ l)%list) => //=.
  apply/andP. split => //=.
  apply is_basic_const_alt => //=.
Qed.

Lemma const_get: forall e,
  is_const e <->
  exists v, e = v_to_e v.
Proof.
  intros e. split; intros H.
  - unfold v_to_e. destruct e => //=; [destruct b => //=| |].
    + exists (VAL_ref (VAL_ref_null r)) => //=.
    + exists (VAL_num v) => //=.
    + exists (VAL_vec v) => //=.
    + exists (VAL_ref (VAL_ref_func f)) => //=.
    + exists (VAL_ref (VAL_ref_extern e)) => //=.
  - destruct H as [v H]. unfold is_const. rewrite H.
    destruct v => //=. destruct v => //=.
Qed.

Lemma const_list_get: forall es,
  const_list es <->
  exists vs, es = v_to_e_list vs.
Proof.
  intros es. split; intros H.
  - unfold v_to_e_list. induction es => //=. by exists [::].
    move/andP in H. destruct H. apply IHes in H0. destruct H0.
    apply const_get in H. destruct H. rewrite H.
    exists (x0 :: x) => //=. by f_equal.
  - destruct H as [vs H]. generalize dependent vs.
    induction es => //=. intros vs H.
    unfold v_to_e_list in H. induction vs => //=.
    rewrite map_cons in H. inversion H.
    fold (v_to_e_list vs) in *. rewrite <- H2. apply IHes in H2.
    apply/andP. split => //=. destruct a0 as [| |[]] => //=.
Qed.

Lemma e_is_trapP : forall e, reflect (e = AI_trap) (e_is_trap e).
Proof.
  case => //= >; by [ apply: ReflectF | apply: ReflectT ].
Qed.

Lemma es_is_trapP : forall l, reflect (l = [::AI_trap]) (es_is_trap l).
Proof.
  intros; unfold es_is_trap; by apply (iffP eqP).
Qed.


Lemma split_n_is_take_drop: forall es n,
    split_n es n = (take n es, drop n es).
Proof.
  move => es n. move: es. elim:n => //=.
  - move => es. by destruct es.
  - move => n IH es'. destruct es' => //=.
    + by rewrite IH.
Qed.



Lemma length_is_size: forall {X:Type} (l: list X),
    length l = size l.
Proof.
  move => X l. by elim: l.
Qed.

Lemma v_to_e_take_exchange: forall vs n,
    v_to_e_list (take n vs) = take n (v_to_e_list vs).
Proof.
  move => vs n. move: vs. elim:n => //=.
  - move => vs. by destruct vs.
  - move => n IH vs'. destruct vs' => //=.
    + by rewrite IH.
Qed.

Lemma v_to_e_drop_exchange: forall vs n,
    v_to_e_list (drop n vs) = drop n (v_to_e_list vs).
Proof.
  move => vs n. move: vs. elim:n => //=.
  - move => vs. by destruct vs.
  - move => n IH vs'. by destruct vs' => //=.
Qed.

Lemma v_to_e_size: forall vs,
    size (v_to_e_list vs) = size vs.
Proof.
  move => vs. elim: vs => //=.
  - move => a l IH. by f_equal.
Qed.      
      
(** This lemma is useful when an instruction consumes some expressions on the stack:
  we usually have to split a list of expressions by the expressions effectively
  consumed by the instructions and the one left. **)
Lemma v_to_e_take_drop_split: forall l n,
  v_to_e_list l = v_to_e_list (take n l) ++ v_to_e_list (drop n l).
Proof.
  move => l n. rewrite v_to_e_cat. by rewrite cat_take_drop.
Qed.

Lemma v_to_e_take: forall l n,
  v_to_e_list (take n l) = take n (v_to_e_list l).
Proof.
  move => + n. induction n => //.
  - move => l. by repeat rewrite take0.
  - move => l. destruct l => //. simpl. f_equal. by apply IHn.
Qed.

Lemma v_to_e_drop: forall l n,
  v_to_e_list (drop n l) = drop n (v_to_e_list l).
Proof.
  move => + n. induction n => //.
  - move => l. by repeat rewrite drop0.
  - move => l. destruct l => //. simpl. f_equal. by apply IHn.
Qed.

Lemma v_to_e_rev: forall l,
  v_to_e_list (rev l) = rev (v_to_e_list l).
Proof.
  elim => //=.
  move => a l IH. rewrite rev_cons. rewrite -cats1. rewrite -v_to_e_cat.
  rewrite rev_cons. rewrite -cats1. by rewrite -IH.
Qed.

Lemma to_b_single_basic_const: forall x,
  is_basic_const x ->
  AI_basic (to_b_single x) = x.
Proof.
  destruct x => //=.
Qed.

Lemma to_b_list_concat: forall es1 es2 : seq administrative_instruction,
    to_b_list (es1 ++ es2) = to_b_list es1 ++ to_b_list es2.
Proof.
  induction es1 => //=.
  move => es2. by f_equal.
Qed.

Lemma to_e_list_basic: forall bes,
    es_is_basic (to_e_list bes).
Proof.
  elim => //=; move => be bes IH.
  apply List.Forall_cons => //.
  by eexists.
Qed.

Lemma basic_concat: forall es1 es2,
    es_is_basic (es1 ++ es2) ->
    es_is_basic es1 /\ es_is_basic es2.
Proof.
  by apply List.Forall_app.
Qed.
  
Lemma basic_split: forall es1 es2,
    es_is_basic es1 ->
    es_is_basic es2 ->
    es_is_basic (es1 ++ es2).
Proof.
  intros; by apply List.Forall_app.
Qed.

Lemma not_basic_concat: forall es1 es2,
    es_all_not_basic (es1 ++ es2) ->
    es_all_not_basic es1 /\ es_all_not_basic es2.
Proof.
  by apply List.Forall_app.
Qed.
  
Lemma not_basic_split: forall es1 es2,
    es_all_not_basic es1 ->
    es_all_not_basic es2 ->
    es_all_not_basic (es1 ++ es2).
Proof.
  intros; by apply List.Forall_app.
Qed.

(* No longer holds because AI_ref, AI_ref_extern are possible consts not in AI_basic *)
(* Could technically create cases for these two every time this is invoked? *)
(*
Lemma const_list_is_basic: forall es,
    const_list es ->
    es_is_basic es.
Proof.
  induction es; try by intros => //=.
  move => H. move/andP in H. destruct H as [H Hs].
  apply IHes in Hs.
  apply List.Forall_cons => //.
  destruct a => //.
  by eexists.
  (* AI_ref, AI_ref_extern *)
Qed.
*)
(*
Lemma const_num_list_is_basic: forall es f e,
    const_list es ->
    (exists es', (es = ([:: AI_ref f] ++ es')
          \/ es = ([:: AI_ref_extern e] ++ es')) -> False)
          \/ es_is_basic es
          \/ es = [::].
Proof.
  intros es f e H. generalize dependent es. induction es; intro H.
  simpl. right. right. reflexivity.
  move/andP in H. destruct H as [H Hs].
  apply IHes in Hs. destruct a eqn: E => //.
  (* destruct Hs as [Hex | [Hbas | Hemp]]. left. apply Hex. *)
  { right. left. simpl. apply List.Forall_cons => //.
    unfold e_is_basic. exists b. reflexivity.
    (* end up needing to prove es_is_basic basis?? *)
    admit. }
  { left. exists es. simpl. intro H'. destruct H'.
    (* somehow use hypothesis to discount AI_ref case? *) admit. }
  { left. exists es. simpl. intro H'. destruct H'.
  (* somehow use hypothesis to discount AI_ref_exitern case? *) admit. }
Admitted.
*)

Lemma to_b_list_rev: forall es : seq administrative_instruction,
    rev (to_b_list es) = to_b_list (rev es).
Proof.
  unfold to_b_list. intros. by rewrite map_rev.
Qed.

Lemma vs_to_vts_cat: forall vs1 vs2,
  vs_to_vts (vs1 ++ vs2) = vs_to_vts vs1 ++ vs_to_vts vs2.
Proof.
  by apply map_cat.
Qed.
  
Lemma vs_to_vts_rev: forall vs,
  vs_to_vts (rev vs) = rev (vs_to_vts vs).
Proof.
  unfold vs_to_vts. intros. by rewrite map_rev.
Qed.

Lemma bes_to_e_list_is_basic: forall bes,
  es_is_basic (to_e_list bes).
Proof.
  induction bes => //=.
  unfold es_is_basic. apply List.Forall_cons => //=.
  unfold e_is_basic. eauto.
Qed.

Lemma const_e_exists: forall e,
    is_const e ->
    exists v, e = v_to_e v.
Proof.
  move => e H.
  unfold is_const in H.
  destruct (e_to_v e) eqn:Hetov => //.
  apply v_to_e_to_v in Hetov; subst.
  by eexists.
Qed.

Lemma basic_const_e_exists: forall e,
    is_basic_const e ->
    exists v, e = v_to_e v.
Proof.
  move => e H.
  unfold is_basic_const in H.
  destruct (e_to_v e) eqn:Hetov => //.
  apply v_to_e_to_v in Hetov; subst.
  destruct v as [| |[]]=> //=.
  - by exists (VAL_num v).
  - by exists (VAL_vec v).
  - by exists (VAL_ref (VAL_ref_null r)).
Qed.

Lemma const_es_exists: forall es,
    const_list es ->
    exists vs, es = v_to_e_list vs.
Proof.
  induction es => //=.
  - by exists [::].
  - move => HConst.
    move/andP in HConst. destruct HConst as [H Hs].
    apply const_e_exists in H.
    destruct H as [v ->].
    apply IHes in Hs as [vs ->].
    by exists (v :: vs).
Qed.

Lemma basic_const_es_exists: forall es,
    basic_const_list es ->
    exists vs, es = v_to_e_list vs.
Proof.
  induction es => //=.
  - by exists [::].
  - move => HConst.
    move/andP in HConst. destruct HConst as [H Hs].
    apply basic_const_e_exists in H.
    destruct H as [v ->].
    remember Hs as Hs'. clear HeqHs'.
    apply IHes in Hs as [vs ->] => //=.
    exists ([::v] ++ vs).
    rewrite -v_to_e_cat. unfold v_to_e_list. simpl. unfold v_to_e.
    destruct v as [| |[]]=> //=.
Qed.

Lemma b_e_elim: forall bes es,
    to_e_list bes = es ->
    bes = to_b_list es /\ es_is_basic es.
Proof.
  move => bes es <-.
  split; last by apply to_e_list_basic.
  unfold to_b_list, to_e_list.
  induction bes => //=; by f_equal.
Qed.

Lemma e_b_elim: forall bes es,
    bes = to_b_list es ->
    es_is_basic es ->
    es = to_e_list bes.
Proof.
  move => bes es -> Hbasic.
  induction es as [ | a es] => //=.
  unfold es_is_basic in Hbasic.
  inversion Hbasic as [|?? H Hs]; subst.
  apply IHes in Hs; rewrite <- Hs.
  destruct a => //; try by destruct H.
Qed.
    
Lemma to_e_list_injective: forall bes bes',
    to_e_list bes = to_e_list bes' ->
    bes = bes'.
Proof.
  move => bes bes' H.
  apply b_e_elim in H; destruct H; subst => //=.
  induction bes' => //=.
  f_equal. apply IHbes'. by apply to_e_list_basic.
Qed.

Lemma to_e_list_cat: forall bes1 bes2,
    to_e_list (bes1 ++ bes2) = to_e_list bes1 ++ to_e_list bes2.
Proof.
  by apply map_cat.
Qed.

(* Maybe there are better/standard tactics for dealing with these, but I didn't find
     anything helpful *)
Lemma concat_cancel_last: forall {X:Type} (l1 l2: seq X) (e1 e2:X),
    l1 ++ [::e1] = l2 ++ [::e2] ->
    l1 = l2 /\ e1 = e2.
Proof.
  move => X l1 l2 e1 e2 H.
  assert (rev (l1 ++ [::e1]) = rev (l2 ++ [::e2])); first by rewrite H.
  repeat rewrite rev_cat in H0. inversion H0.
  rewrite - (revK l1). rewrite H3. split => //. by apply revK.
Qed.

Lemma concat_cancel_last_n: forall (l1 l2 l3 l4: seq value_type),
    l1 ++ l2 = l3 ++ l4 ->
    size l2 = size l4 ->
    (l1 == l3) && (l2 == l4).
Proof.
  move => l1 l2 l3 l4 HCat HSize.
  rewrite -eqseq_cat; first by apply/eqP.
  assert (size (l1 ++ l2) = size (l3 ++ l4)); first by rewrite HCat.
  repeat rewrite size_cat in H.
  rewrite HSize in H. by lias.
Qed.

Lemma extract_list1 : forall {X:Type} (es: seq X) (e1 e2:X),
    es ++ [::e1] = [::e2] ->
    es = [::] /\ e1 = e2.
Proof.
  move => X es e1 e2 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma extract_list2 : forall {X:Type} (es: seq X) (e1 e2 e3:X),
    es ++ [::e1] = [::e2; e3] ->
    es = [::e2] /\ e1 = e3.
Proof.
  move => X es e1 e2 e3 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma extract_list3 : forall {X:Type} (es: seq X) (e1 e2 e3 e4:X),
    es ++ [::e1] = [::e2; e3; e4] ->
    es = [::e2; e3] /\ e1 = e4.
Proof.
  move => X es e1 e2 e3 e4 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma extract_list4 : forall {X:Type} (es: seq X) (e1 e2 e3 e4 e5:X),
    es ++ [::e1] = [::e2; e3; e4; e5] ->
    es = [::e2; e3; e4] /\ e1 = e5.
Proof.
  move => X es e1 e2 e3 e4 e5 H.
  apply concat_cancel_last.
  by apply H.
Qed.

Lemma list_nth_prefix: forall {X:Type} (l1 l2: seq X) x,
    List.nth_error (l1 ++ [::x] ++ l2) (length l1) = Some x.
Proof.
  move => X. by induction l1 => //=.
Qed.


(** * Tactics **)

(** [gen_ind] perform an induction over predicates like [be_typing], generalising its parameters,
  but not generalising any section variables such as [host_function].
  The reason for this tactic is that [dependent induction] is far too aggressive
  in its generalisation, and prevents the use of some lemmas. **)

(** The first step is to name each parameter of the predicate. **)
Ltac gen_ind_pre H :=
  let rec aux v :=
    lazymatch v with
    | ?f ?x =>
      let only_do_if_ok_direct t cont :=
        lazymatch t with
        | Type => idtac
        | host _ => idtac
        | _ => cont tt
        end in
      let t := type of x in
      only_do_if_ok_direct t ltac:(fun _ =>
        let t :=
          match t with
          | _ _ => t
          | ?t => eval unfold t in t
          | _ => t
          end in
        only_do_if_ok_direct t ltac:(fun _ =>
          let x' :=
            let rec get_name x :=
              match x with
              | ?f _ => get_name f
              | _ => fresh x
              | _ => fresh "x"
              end in
            get_name x in
          move: H;
          set_eq x' x;
          let E := fresh "E" x' in
          move=> E H));
      aux f
    | _ => idtac
    end in
  let Ht := type of H in
  aux Ht.

(** Then, each of the associated parameters can be generalised. **)
Ltac gen_ind_gen H :=
  let rec try_generalize t :=
    lazymatch t with
    | ?f ?x => try_generalize f; try_generalize x
    | ?x => is_variable x ltac:(generalize dependent x) ltac:(idtac)
    | _ => fail "unable to generalize" t
    end in
  let rec aux v :=
    lazymatch v with
    | ?f ?x => 
    lazymatch goal with
      | _ : x = ?y |- _ => try_generalize y
      | _ => fail "unexpected term" v
      end;
      aux f
    | _ => idtac
    end in
  let Ht := type of H in
  aux Ht.

(** After the induction, one can inverse them again (and do some cleaning). **)
Ltac gen_ind_post :=
  repeat lazymatch goal with
  | |- _ = _ -> _ => inversion 1
  | |- _ -> _ => intro
  end;
  repeat lazymatch goal with
  | H: True |- _ => clear H
  | H: ?x = ?x |- _ => clear H
  end.

(** Wrapping every part of the generalised induction together. **)
Ltac gen_ind H :=
  gen_ind_pre H;
  gen_ind_gen H;
  induction H;
  gen_ind_post.

(** Similar to [gen_ind H; subst], but cleaning just a little bit more. **)
Ltac gen_ind_subst H :=
  gen_ind H;
  subst;
  gen_ind_post.

(** Calls the continuation on [v] or, if it failed, on [v] whose root has been unfolded.
  This is useful for tactics with pattern mtaching recognising a predicate which is
  frequently folded in a section, like [be_typing]. **)
Ltac call_unfold v cont :=
  let rec unfold_root :=
    lazymatch v with
    | ?f ?x =>
      let f := unfold_root f in
      constr:(f x)
    | ?x => eval unfold x in x
    end in
  first [
      cont v
    | let v := unfold_root v in
      cont v ].

(** Perform basic simplifications of [es_is_basic]. **)
Ltac basic_inversion :=
   repeat lazymatch goal with
         | H: True |- _ =>
           clear H
         | H: es_is_basic (_ ++ _) |- _ =>
           let Ha := fresh H in
           let Hb := fresh H in
           apply basic_concat in H; destruct H as [Ha Hb]
         | H: es_is_basic [::] |- _ =>
           clear H
         | H: es_is_basic [::_] |- _ =>
           let Hcontra := fresh "Hcontra" in
            try by (inversion H as [|?? Hcontra]; destruct Hcontra as [? Hcontra]; inversion Hcontra)
         | H: e_is_basic _ |- _ =>
           inversion H; try by []
         end.

(** Rewrite hypotheses on the form [_ ++ [:: _] = _] as some easier to use equalities. **)
Ltac extract_listn :=
  repeat lazymatch goal with
  | H: (?es ++ [::?e])%list = [::_] |- _ =>
    apply extract_list1 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_] |- _ =>
    apply extract_list1 in H; destruct H; subst
  | H: (?es ++ [::?e])%list = [::_; _] |- _ =>
    apply extract_list2 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_; _] |- _ =>
    apply extract_list2 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_; _; _] |- _ =>
    apply extract_list3 in H; destruct H; subst
  | H: (?es ++ [::?e])%list = [::_; _; _] |- _ =>
    apply extract_list3 in H; destruct H; subst
  | H: (?es ++ [::?e])%list = [::_; _; _; _] |- _ =>
    apply extract_list4 in H; destruct H; subst
  | H: ?es ++ [::?e] = [::_; _; _; _] |- _ =>
    apply extract_list4 in H; destruct H; subst
  | H: _ :: _ = (_ ++ _)%list |- _ => symmetry in H
  | H: _ :: _ = _ ++ _ |- _ => symmetry in H
         end.


Ltac fold_upd_context :=
  lazymatch goal with
  | |- context [upd_local (upd_return ?C ?ret) ?loc] =>
    replace (upd_local (upd_return C ret) loc) with
        (upd_local_label_return C loc (tc_label C) ret); try by destruct C
  | |- context [upd_return (upd_local ?C ?loc) ?ret] =>
    replace (upd_return (upd_local C loc) ret) with
        (upd_local_label_return C loc (tc_label C) ret); try by destruct C
  end.



(** * More Advanced Lemmas **)

Section Host.

Variable host_function : eqType.

Let store_record := store_record host_function.
Let function_closure := function_closure host_function.
Let e_typing : store_record -> t_context -> seq administrative_instruction -> function_type -> Prop :=
  @e_typing _.

(*
Lemma lfilled_collapse1: forall n lh vs es LI l,
    lfilledInd n lh (vs++es) LI ->
    const_list vs ->
    length vs >= l ->
    exists lh', lfilledInd n lh' ((drop (length vs-l) vs) ++ es) LI.
Proof.
  move => n lh vs es LI l HLF HConst HLen.
  (* Comparing this proof to the original proof in Isabelle, it seems that (induction X rule: Y) in Isabelle means induction on proposition Y remembering X (in Coq). *)
  remember (vs++es) as es'. induction HLF; subst.
  - exists (LH_base (vs0 ++ (take (length vs - l) vs)) es').
    (* The proof to this case should really have finished here; the below is just rearranging brackets and applying cat_take_drop and assumptions. *)
    replace (vs0++(vs++es)++es') with ((vs0++take (length vs - l) vs) ++ (drop (length vs - l) vs ++ es) ++ es').
    { apply LfilledBase. apply const_list_concat => //=.
      by apply const_list_take. }
    repeat rewrite -catA. f_equal.
    repeat rewrite catA. do 2 f_equal.
    by apply cat_take_drop. 
  - destruct IHHLF => //. eexists (LH_rec _ _ _ _ _). apply LfilledRec => //. by apply H0.
Qed.

Lemma lfilled_collapse2: forall n lh es es' LI,
    lfilledInd n lh (es++es') LI ->
    exists lh', lfilledInd n lh' es LI.
Proof.
  move => n lh es es' LI HLF. remember (es ++ es') as Ees. induction HLF; subst.
  - eexists (LH_base _ _). rewrite <- catA. by apply LfilledBase.
  - destruct IHHLF => //. eexists (LH_rec _ _ _ _ _). apply LfilledRec => //. by apply H0.
Qed.

Lemma lfilled_collapse3: forall k lh n les es LI,
    lfilledInd k lh [:: AI_label n les es] LI ->
    exists lh', lfilledInd (k+1) lh' es LI.
Proof.
  move => k lh n les es LI HLF. remember [:: AI_label n les es] as E.  induction HLF; subst.
  - eexists (LH_rec _ _ _ _ _). apply LfilledRec. auto.
    assert (lfilledInd 0 (LH_base nil nil) es ([::] ++ es ++ [::])). { by apply LfilledBase. }
    simpl in H0. rewrite cats0 in H0. by apply H0.
  - destruct IHHLF => //. eexists (LH_rec _ _ _ _ _). apply LfilledRec => //. by apply H0.
Qed.
 *)

Lemma lfilled_deterministic: forall k (lh: lholed k) es les les',
    lfilled lh es les ->
    lfilled lh es les' ->
    les = les'.
Proof.
  unfold lfilled in *.
  intros ????? Hlf1 Hlf2.
  move/eqP in Hlf1.
  move/eqP in Hlf2.
  by subst.
Qed.  

Lemma all_projection: forall {X:Type} f (l:seq X) n x,
    all f l ->
    List.nth_error l n = Some x ->
    f x.
Proof.
  move => X f l n x.
  move: l.
  induction n => //; destruct l => //=; move => HF HS; remove_bools_options => //.
  eapply IHn; by eauto.
Qed.

Lemma all2_projection: forall {X Y:Type} f (l1:seq X) (l2:seq Y) n x1 x2,
    all2 f l1 l2 ->
    List.nth_error l1 n = Some x1 ->
    List.nth_error l2 n = Some x2 ->
    f x1 x2.
Proof.
  move => X Y f l1 l2 n.
  move: l2 l1.
  induction n => //=; move => l2 l1 x1 x2 HALL HN1 HN2.
  - destruct l1 => //=. destruct l2 => //=.
    inversion HN1. inversion HN2. subst. clear HN1. clear HN2.
    simpl in HALL. move/andP in HALL. by destruct HALL.
  - destruct l1 => //=. destruct l2 => //=.
    simpl in HALL. move/andP in HALL. destruct HALL.
    eapply IHn; by eauto.
Qed.

Definition function {X Y:Type} (f: X -> Y -> Prop) : Prop :=
  forall x y1 y2, ((f x y1 /\ f x y2) -> y1 = y2).

Lemma all2_function_unique: forall {X Y:Type} f (l1:seq X) (l2 l3:seq Y),
    all2 f l1 l2 ->
    all2 f l1 l3 ->
    function f ->
    l2 = l3.
Proof.
  move => X Y f l1.
  induction l1 => //=; move => l2 l3 HA1 HA2 HF.
  - destruct l2 => //. by destruct l3 => //.
  - destruct l2 => //=; destruct l3 => //=.
    simpl in HA1. simpl in HA2.
    move/andP in HA1. move/andP in HA2.
    destruct HA1. destruct HA2.
    unfold function in HF.
    assert (y = y0); first by eapply HF; eauto.
    rewrite H3. f_equal.
    by apply IHl1.
Qed.


(** The decreasing measure used in the definition of [lfilled_pickable_rec_gen]. **)
Definition lfilled_pickable_rec_gen_measure (LI : seq administrative_instruction) :=
  TProp.max
    (seq_administrative_instruction_rect'
       (fun _ => 0)
       0
       (fun _ => 0)
       (fun _ => 0)
       (fun _ => 0)
       (fun _ LI1 LI2 m1 m2 => 1 + TProp.max m2)
       (fun _ _ LI' m => 0)
       LI).

Lemma lfilled_pickable_rec_gen_measure_cons : forall I LI,
  lfilled_pickable_rec_gen_measure LI <= lfilled_pickable_rec_gen_measure (I :: LI).
Proof.
  move=> I LI. by apply: leq_maxr.
Qed.

Lemma lfilled_pickable_rec_gen_measure_concat_l : forall LI1 LI2,
  lfilled_pickable_rec_gen_measure LI1 <= lfilled_pickable_rec_gen_measure (LI1 ++ LI2).
Proof.
  move => LI1 LI2. induction LI1 => /=.
  - rewrite {1} /lfilled_pickable_rec_gen_measure /=. by lias.
  - rewrite /lfilled_pickable_rec_gen_measure /=.
    by apply: maxn_congruence_r.
Qed.

Lemma lfilled_pickable_rec_gen_measure_concat_r : forall LI1 LI2,
  lfilled_pickable_rec_gen_measure LI2 <= lfilled_pickable_rec_gen_measure (LI1 ++ LI2).
Proof.
  move => LI1 LI2. induction LI1 => /=.
  - rewrite {1} /lfilled_pickable_rec_gen_measure /=. by lias.
  - rewrite /lfilled_pickable_rec_gen_measure /=. eapply leq_trans; first by apply: IHLI1.
    by apply: leq_maxr.
Qed.

(*
Lemma lfilled_pickable_rec_gen_measure_label_r : forall n es LI LI',
  lfilled_pickable_rec_gen_measure LI < lfilled_pickable_rec_gen_measure (AI_label n es LI :: LI').
Proof.
  move=> n es LI LI'. rewrite /lfilled_pickable_rec_gen_measure /=. by apply: leq_maxl.
Qed.

(** A helper definition for [lfilled_decidable_rec]. **)
Definition lfilledInd_pickable_rec_gen : forall fes,
  (forall es' lh lh' n0, decidable (lfilledInd 0 lh (fes n0 lh') es')) ->
  forall es', pickable2 (fun n lh => lfilledInd n lh (fes n lh) es').
Proof.
  move=> fes D0 es'.
  apply: (@pickable2_equiv _ _ (fun n lh => lfilledInd n lh (fes (0+n) lh) es')); first by [].
  move: 0 => k.
  have [m E]: { m | lfilled_pickable_rec_gen_measure es' = m }; first by eexists.
  move: fes D0 es' E k. strong induction m. rename X into IH. move=> fes D0 es' E k.
  have Dcl: forall vs, decidable (const_list vs).
  { move=> vs. by apply: is_true_decidable. }
  (** First, we check whether we can set [n = 0]. **)
  have P0: pickable2 (fun vs es'' =>
                       let lh := LH_base vs es'' in
                       let es := fes k lh in
                       es' = vs ++ es ++ es'' /\ const_list vs /\ lfilledInd 0 lh es es').
  {
    have: pickable3 (fun vs es es'' =>
      es' = vs ++ es ++ es'' /\ let lh := LH_base vs es'' in
      es = fes k lh /\ const_list vs /\ lfilledInd 0 lh es es').
    {
      apply: list_split_pickable3_gen. move=> vs es es'' Ees /=.
      case E': (es == fes k (LH_base vs es'')); move/eqP: E' => E'.
      - rewrite E'. repeat apply: decidable_and => //. by apply: eq_comparable.
      - right. by move=> [Ees2 [Cl I]].
    }
    case.
    - move=> [[[vs es] es''] [E1 [E2 [Cl I]]]]. left. exists (vs, es''). by subst.
    - move=> Ex. right. move=> [vs [es'' [E' [Cl I]]]]. apply: Ex.
      by repeat eexists; eassumption.
  }
  case P0.
  {
    move=> [[vs es''] [E' [Cvs I]]]. left. exists (0, LH_base vs es'').
    subst. rewrite_by (k + 0 = k). by apply: LfilledBase.
  }
  move=> nE.
  (** Otherwise, we have to apply [LfilledRec]. **)
  have Dparse: forall es' : seq administrative_instruction,
    decidable (exists n es1 LI es2, es' = [:: AI_label n es1 LI] ++ es2).
  {
    clear. move=> es'.
    have Pparse: pickable4 (fun n es1 LI es2 => es' = [:: AI_label n es1 LI] ++ es2).
    {
      let no := by intros; right; intros (?&?&?&?&?) in
      (case es'; first by no); case; try by no.
      move=> n l1 l2 l3. left. by exists (n, l1, l2, l3).
    }
    convert_pickable Pparse.
  }
  case: (list_split_pickable2 (fun vs es => decidable_and (Dcl vs) (Dparse es)) es').
  - move=> [[vs es''] [E1 [C Ex]]].
    destruct es'' as [| [| | | n es1 LI |] es2];
      try solve [ exfalso; move: Ex => [? [? [? [? E']]]]; inversion E' ].
    clear Ex. rewrite E1.
    have I_LI: (lfilled_pickable_rec_gen_measure LI < m)%coq_nat.
    {
      rewrite -E E1. apply/leP. eapply leq_trans.
      - by eapply lfilled_pickable_rec_gen_measure_label_r.
      - by apply: lfilled_pickable_rec_gen_measure_concat_r.
    }
    set fes' := fun k lh => fes (k + 1) (LH_rec vs n es1 lh es2).
    have D1: forall es' lh lh' n0, decidable (lfilledInd 0 lh (fes' n0 lh') es').
    { move=> ? ? ? ?. by apply: D0. }
    move: (IH _ I_LI fes' D1 LI (erefl _) k) => [[[n' lh] LF]|NP].
    - eapply LfilledRec with (vs := vs) in LF => //.
      left. exists (n'.+1, LH_rec vs n es1 lh es2).
      move: LF. rewrite /fes'. rewrite_by (k + n' + 1 = k + n'.+1) => /= LF. by apply: LF.
    - right. move=> [n' [lh FI]]. apply: NP. inversion FI; subst.
      + exfalso. apply: nE. exists vs0. exists es'0. repeat split => //.
        * rewrite -H. by rewrite_by (k + 0 = k).
        * by rewrite_by (k = k + 0).
      + apply const_list_concat_inv in H => //. move: H => [? [E ?]]. inversion E; subst.
        exists k0. eexists. rewrite /fes'. rewrite_by (k + k0 + 1 = k + k0.+1). by apply: H4.
  - move=> nE'. right. move=> [n [lh I]]. inversion I; subst.
    + apply: nE. do 2 eexists. rewrite_by (k + 0 = k). repeat split; try eassumption.
      by apply: LfilledBase.
    + apply: nE'. by repeat eexists.
Defined.

Definition lfilled_pickable_rec_gen : forall fes,
  (forall es' lh lh' n0, decidable (lfilled 0 lh (fes n0 lh') es')) ->
  forall es', pickable2 (fun n lh => lfilled n lh (fes n lh) es').
Proof.
  move=> fes D0 es'.
  apply: (@pickable2_equiv _ _ (fun n lh => lfilledInd n lh (fes (0+n) lh) es')).
  { move=> n lh. by split; apply lfilled_Ind_Equivalent. }
  apply: lfilledInd_pickable_rec_gen => es'' lh lh' n0.
  by apply: decidable_equiv; first by apply: lfilled_Ind_Equivalent.
Defined.

(** We can always decide [lfilled 0]. **)
Lemma lfilled_decidable_base : forall es es' lh,
  decidable (lfilled 0 lh es es').
Proof.
  move=> es es' lh. apply: (@decidable_equiv (lfilledInd 0 lh es es')).
  { by split; apply lfilled_Ind_Equivalent. }
  case lh.
  - move=> vsh esh.
    have: pickable2 (fun vs es'' => es' = vs ++ es ++ es'' /\ const_list vs /\ vs = vsh /\ es'' = esh).
    {
      apply: list_search_split_pickable2.
      - by apply: administrative_instruction_eq_dec.
      - move=> ? ?. by repeat apply: decidable_and; apply: eq_comparable.
    }
    case.
    + move=> [[vs es''] [E [C [E1 E2]]]]. left. subst. by constructor.
    + move=> nE. right. move=> I. apply: nE. inversion I. subst. by repeat eexists.
  - move=> vs n es'' lh' es'''. right. move=> I. by inversion I.
Defined.

(** We can furthermore rebuild the stack [lh] for any [lfilled 0] predicate. **)
Lemma lfilled_pickable_base : forall es es',
  pickable (fun lh => lfilled 0 lh es es').
Proof.
  move=> es es'. apply: (@pickable_equiv _ (fun lh => lfilledInd 0 lh es es')).
  { move=> lh. by split; apply lfilled_Ind_Equivalent. }
  have: pickable2 (fun vs es'' => es' = vs ++ es ++ es'' /\ const_list vs /\ True).
  {
    apply: list_search_split_pickable2.
    - by apply: administrative_instruction_eq_dec.
    - move=> ? ?. apply: decidable_and.
      + by apply: is_true_decidable.
      + by left.
  }
  case.
  - move=> [[vs es''] [E [C _]]]. left. eexists. subst. by constructor.
  - move=> nE. right. move=> [lh I]. apply: nE. inversion I. subst. by repeat eexists.
Defined.
 

(** A helper definition for the decidability of [br_reduce] and [return_reduce]
  (see type_soundness.v). **)
Definition lfilled_pickable_rec : forall es,
  (forall es' lh, decidable (lfilled 0 lh es es')) ->
  forall es', pickable2 (fun n lh => lfilled n lh es es').
Proof.
  move=> es D. by apply: lfilled_pickable_rec_gen.
Defined.
 *)

Lemma lfilled_decidable {k: nat}: forall (lh: lholed k) es es',
  decidable (lfilled lh es es').
Proof.
  intros; by decidable_equality.
Qed.

(* A reformulation of [ety_a] that is easier to be used. *)
Lemma ety_a': forall s C es ts,
    es_is_basic es ->
    be_typing C (to_b_list es) ts ->
    e_typing s C es ts.
Proof.
  move => s C es ts HBasic HType.
  replace es with (to_e_list (to_b_list es)).
  - by apply ety_a.
  - symmetry. by apply e_b_elim.
Qed.

(* Some quality of life lemmas *)
Lemma bet_weakening_empty_1: forall C es ts t2s,
    be_typing C es (Tf [::] t2s) ->
    be_typing C es (Tf ts (ts ++ t2s)).
Proof.
  move => C es ts t2s HType.
  assert (be_typing C es (Tf (ts ++ [::]) (ts ++ t2s))) as H; first by apply bet_weakening.
  by rewrite cats0 in H.
Qed.

Lemma et_weakening_empty_1: forall s C es ts t2s,
    e_typing s C es (Tf [::] t2s) ->
    e_typing s C es (Tf ts (ts ++ t2s)).
Proof.
  move => s C es ts t2s HType.
  assert (e_typing s C es (Tf (ts ++ [::]) (ts ++ t2s))) as H; first by apply ety_weakening.
  by rewrite cats0 in H.
Qed.

Lemma bet_weakening_empty_2: forall C es ts t1s,
    be_typing C es (Tf t1s [::]) ->
    be_typing C es (Tf (ts ++ t1s) ts).
Proof.
  move => C es ts t1s HType.
  assert (be_typing C es (Tf (ts ++ t1s) (ts ++ [::]))) as H; first by apply bet_weakening.
  by rewrite cats0 in H.
Qed.

Lemma bet_weakening_empty_both: forall C es ts,
    be_typing C es (Tf [::] [::]) ->
    be_typing C es (Tf ts ts).
Proof.
  move => C es ts HType.
  assert (be_typing C es (Tf (ts ++ [::]) (ts ++ [::]))) as H; first by apply bet_weakening.
  by rewrite cats0 in H.
Qed.

Lemma empty_typing: forall C t1s t2s,
    be_typing C [::] (Tf t1s t2s) ->
    t1s = t2s.
Proof.
  move => C t1s t2s HType.
  gen_ind_subst HType => //.
  - by destruct es. (* discriminate Enil. *)
  - f_equal. by eapply IHHType.
Qed.

Lemma e_empty_typing: forall s C t1s t2s,
    e_typing s C [::] (Tf t1s t2s) ->
    t1s = t2s.
Proof.
  move => s C t1s t2s HType.
  gen_ind_subst HType => //.
  - induction bes.
    inversion H; subst => //=.
    induction es => //=.
    by apply empty_typing in H.
  - apply IHbes; inversion Enil.
  - induction es. eapply IHHType1 => //=. discriminate Enil.
  - f_equal. eapply IHHType => //=.
Qed.

Lemma et_to_bet: forall s C es ts,
    es_is_basic es ->
    e_typing s C es ts ->
    be_typing C (to_b_list es) ts.
Proof.
  move => s C es ts HBasic HType.
  dependent induction HType; basic_inversion.
  + replace (to_b_list (to_e_list bes)) with bes => //.
    by apply b_e_elim.
  + rewrite to_b_list_concat.
    eapply bet_composition.
    * by eapply IHHType1 => //.
    * by eapply IHHType2 => //.
  + apply bet_weakening. by eapply IHHType => //.
Qed.

Section composition_typing_proofs.

Hint Constructors be_typing : core.

(** A helper tactic for proving [composition_typing_single]. **)
Ltac auto_prove_bet:=
  repeat lazymatch goal with
  | H: _ |- exists ts t1s t2s t3s, ?tn = ts ++ t1s /\ ?tm = ts ++ t2s /\
                                   be_typing _ [::] (Tf _ _) /\ _ =>
    try exists [::], tn, tm, tn; try eauto
  | H: _ |- _ /\ _ =>
    split => //=; try eauto
  | H: _ |- be_typing _ [::] (Tf ?es ?es) =>
    apply bet_weakening_empty_both; try by []
  end.

Lemma composition_typing_single: forall C es1 e t1s t2s,
    be_typing C (es1 ++ [::e]) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             be_typing C es1 (Tf t1s' t3s) /\
                             be_typing C [::e] (Tf t3s t2s').
Proof.
  move => C es1 e t1s t2s HType.
  gen_ind_subst HType; extract_listn; auto_prove_bet.
  + by destruct es1 => //=.
  + apply concat_cancel_last in H1. destruct H1. subst.
    by exists [::], t1s0, t2s0, t2s.
  + edestruct IHHType; eauto.
    destruct H as [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]. subst.
    exists (ts ++ x), t1s', t2s', t3s'.
    by repeat split => //=; rewrite -catA.
Qed.

Lemma composition_typing: forall C es1 es2 t1s t2s,
    be_typing C (es1 ++ es2) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             be_typing C es1 (Tf t1s' t3s) /\
                             be_typing C es2 (Tf t3s t2s').
Proof.
  move => C es1 es2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1.
  clear Heqes2'. subst.
  induction es2' => //=; move => es1 t1s t2s HType.
  - unfold rev in HType; simpl in HType. subst.
    rewrite cats0 in HType.
    exists [::], t1s, t2s, t2s.
    repeat split => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - rewrite rev_cons in HType.
    rewrite -cats1 in HType. subst.
    rewrite catA in HType.
    apply composition_typing_single in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]]. subst.
    apply IHes2' in H3.
    destruct H3 as [ts2 [t1s2 [t2s2 [t3s2 [H5 [H6 [H7 H8]]]]]]]. subst.
    exists ts', (ts2 ++ t1s2), t2s', (ts2 ++ t3s2).
    repeat split => //.
    + by apply bet_weakening.
    + rewrite rev_cons. rewrite -cats1.
      eapply bet_composition; eauto.
      by apply bet_weakening.
Qed.

(* helper lemma for the more general variant *)
Lemma e_composition_typing_single: forall s C es1 e t1s t2s,
    e_typing s C (es1 ++ [::e]) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             e_typing s C es1 (Tf t1s' t3s) /\
                             e_typing s C [::e] (Tf t3s t2s').
Proof.
  move => s C es1 es2 t1s t2s HType.
  gen_ind_subst HType; extract_listn.
  - (* basic *)
    apply b_e_elim in H3. destruct H3. subst.
    rewrite to_b_list_concat in H.
    apply composition_typing in H.
    apply basic_concat in H1. destruct H1.
    destruct H as [ts' [t1s' [t2s' [t3s' [H2 [H3 [H4 H5]]]]]]]. subst.
    exists ts', t1s', t2s', t3s'.
    by repeat split => //=; apply ety_a' => //=.
  - (* composition *)
    apply concat_cancel_last in H2. destruct H2. subst.
    by exists [::], t1s0, t2s0, t2s.
  - (* weakening *)
    edestruct IHHType; eauto.
    destruct H as [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]. subst.
    exists (ts ++ x), t1s', t2s', t3s'.
    by repeat split => //; rewrite catA.
  - (* Trap *)
    exists [::], t1s, t2s, t1s.
    repeat split => //=.
    + apply ety_a' => //. apply bet_weakening_empty_both. by apply bet_empty.
    + by apply ety_trap.
  - (* External ref *)
    exists [::], [::], [::T_ref T_externref], [::]. repeat split => //=.
    + by apply ety_a'.
    + by apply ety_ref_extern.
  - (* Funcref *)
    exists [::], [::], [::T_ref T_funcref], [::]. repeat split => //=.
    + by apply ety_a'.
    + by eapply ety_ref; apply H.
  - (* Invoke *)
    exists [::], t1s, t2s, t1s. repeat split => //=.
    + apply ety_a' => //. apply bet_weakening_empty_both. by apply bet_empty.
    + by eapply ety_invoke; eauto.
  - (* Label *)
    exists [::], [::], t2s0, [::]. repeat split => //=.
    + by apply ety_a' => //.
    + by eapply ety_label; eauto.
  - (* Local *)
    exists [::], [::], t2s, [::]. repeat split => //=.
    + by apply ety_a' => //.
    + by apply ety_local.
Qed.

(* only basic instructions consume the stack *)
Lemma e_composition_typing_single_not_basic: forall s C es1 e t1s t2s,
    e_typing s C (es1 ++ [::e]) (Tf t1s t2s) ->
    e_not_basic e ->
    exists t3s, e_typing s C es1 (Tf t1s t3s) /\
                e_typing s C [::e] (Tf t3s t2s).
Proof.
  move => s C es1 e t1s t2s HType.
  gen_ind_subst HType; extract_listn.
  - (* basic *)
    apply b_e_elim in H3. destruct H3.
    apply basic_concat in H1. destruct H1.
    unfold es_is_basic in H2. unfold e_not_basic in H4.
    apply List.Forall_inv in H2 => //.
  - (* composition *)
    apply concat_cancel_last in H2. destruct H2. subst.
    by exists t2s.
  - (* weakening *)
    edestruct IHHType; eauto.
    destruct H as [H H']. subst.
    exists (ts ++ x).
    by repeat split => //; apply ety_weakening.
  - (* Trap *)
    exists t1s.
    repeat split => //=.
    + apply ety_a' => //. apply bet_weakening_empty_both. by apply bet_empty.
    + by apply ety_trap.
  - (* External ref *)
    exists [::]. repeat split => //=.
    + by apply ety_a'.
    + by apply ety_ref_extern.
  - (* Funcref *)
    exists [::]. repeat split => //=.
    + by apply ety_a'.
    + by eapply ety_ref; apply H.
  - (* Invoke *)
    exists t1s. repeat split => //=.
    + apply ety_a' => //. apply bet_weakening_empty_both. by apply bet_empty.
    + by eapply ety_invoke; eauto.
  - (* Label *)
    exists [::]. repeat split => //=.
    + by apply ety_a' => //.
    + by eapply ety_label; eauto.
  - (* Local *)
    exists [::]. repeat split => //=.
    + by apply ety_a' => //.
    + by apply ety_local.
Qed.

Lemma e_composition_typing: forall s C es1 es2 t1s t2s,
    e_typing s C (es1 ++ es2) (Tf t1s t2s) ->
    exists ts t1s' t2s' t3s, t1s = ts ++ t1s' /\
                             t2s = ts ++ t2s' /\
                             e_typing s C es1 (Tf t1s' t3s) /\
                             e_typing s C es2 (Tf t3s t2s').
Proof.
  move => s C es1 es2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1.
  clear Heqes2'. subst.
  induction es2' => //=; move => es1 t1s t2s HType.
  - unfold rev in HType; simpl in HType.
    rewrite cats0 in HType.
    exists [::], t1s, t2s, t2s.
    repeat split => //=.
    apply ety_a'; first by unfold rev => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - rewrite rev_cons in HType.
    rewrite -cats1 in HType. subst.
    rewrite catA in HType.
    apply e_composition_typing_single in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]]. subst.
    apply IHes2' in H3.
    destruct H3 as [ts2 [t1s2 [t2s2 [t3s2 [H5 [H6 [H7 H8]]]]]]]. subst.
    exists ts', (ts2 ++ t1s2), t2s', (ts2 ++ t3s2).
    repeat split => //.
    + by apply ety_weakening.
    + rewrite rev_cons. rewrite -cats1.
      eapply ety_composition; eauto.
      by apply ety_weakening.
Qed.

Lemma e_composition_typing_all_not_basic: forall s C es1 es2 t1s t2s,
    e_typing s C (es1 ++ es2) (Tf t1s t2s) ->
    es_all_not_basic es2 ->
    exists t3s, e_typing s C es1 (Tf t1s t3s) /\
                e_typing s C es2 (Tf t3s t2s).
Proof.
  move => s C es1 es2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1.
  clear Heqes2'. subst.
  induction es2' => //=; move => es1 t1s t2s HType.
  - unfold rev in HType; simpl in HType.
    rewrite cats0 in HType.
    exists t2s.
    repeat split => //=.
    apply ety_a'; first by unfold rev => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - rewrite rev_cons in HType.
    rewrite -cats1 in HType. subst.
    rewrite catA in HType.
    intros.
    apply e_composition_typing_single_not_basic in HType => //=.
    2: {
      unfold rev in H; simpl in H; rewrite catrevE in H.
      apply not_basic_concat in H. destruct H.
      unfold es_all_not_basic in H0. apply List.Forall_inv in H0 => //.
    }
    destruct HType as [t3s [H1 H2]]. subst.
    apply IHes2' in H1.
    2: {
      unfold rev in H; simpl in H; rewrite catrevE in H.
      apply not_basic_concat in H. destruct H.
      unfold es_all_not_basic in H0. apply List.Forall_inv in H0 => //.
    }
    destruct H1 as [t3s' [H1' H2']]. subst.
    exists t3s'.
    repeat split => //.
    + rewrite rev_cons. rewrite -cats1.
      eapply ety_composition; eauto.
Qed.

Lemma e_composition_typing_const_list: forall s C vs es2 t1s t2s,
    e_typing s C ((v_to_e_list vs) ++ es2) (Tf t1s t2s) ->
    exists t3s, e_typing s C (v_to_e_list vs) (Tf t1s t3s) /\
                e_typing s C es2 (Tf t3s t2s).
Proof.
  move => s C vs es2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent vs.
  clear Heqes2'. subst.
  induction es2' => //=; move => vs t1s t2s HType.
  - unfold rev in HType; simpl in HType.
    rewrite cats0 in HType.
    exists t2s.
    repeat split => //=.
    apply ety_a'; first by unfold rev => //=.
    apply bet_weakening_empty_both.
    by apply bet_empty.
  - rewrite rev_cons in HType.
    rewrite -cats1 in HType. subst.
    rewrite catA in HType.
    apply e_composition_typing_single in HType.
    destruct HType as [ts' [t1s' [t2s' [t3s' [H1 [H2 [H3 H4]]]]]]]. subst.
    intros.
    apply IHes2' in H3 => //=.
    destruct H3 as [t3s2 [H5 H6]]. subst.
    exists (ts' ++ t3s2).
    repeat split => //.
    + by apply ety_weakening.
    + rewrite rev_cons. rewrite -cats1.
      eapply ety_composition with (t2s := (ts' ++ t3s')); eauto;
      by apply ety_weakening.
Qed.

Lemma bet_composition': forall C es1 es2 t1s t2s t3s,
    be_typing C es1 (Tf t1s t2s) ->
    be_typing C es2 (Tf t2s t3s) ->
    be_typing C (es1 ++ es2) (Tf t1s t3s).
Proof.
  move => C es1 es2 t1s t2s t3s HType1 HType2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1. generalize dependent es2.
  generalize dependent t1s. generalize dependent t2s.
  generalize dependent t3s.
  induction es2' => //=.
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1. destruct es2 => //=. rewrite cats0.
    apply empty_typing in HType2. by subst.
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1.
    rewrite rev_cons in H2. rewrite -cats1 in H2.
    rewrite H2 in HType2.
    apply composition_typing in HType2.
    destruct HType2 as [ts [t1s' [t2s' [t3s' [H3 [H4 [H5 H6]]]]]]]. subst.
    rewrite catA. eapply bet_composition => //=.
    instantiate (1 := (ts ++ t3s')).
    eapply IHes2' => //.
    instantiate (1 := (ts ++ t1s')); first by apply bet_weakening.
    symmetry. by apply revK.
    by apply HType1.
    by apply bet_weakening.
Qed.

Lemma bet_composition_front: forall C e es t1s t2s t3s,
    be_typing C [::e] (Tf t1s t2s) ->
    be_typing C es (Tf t2s t3s) ->
    be_typing C (e :: es) (Tf t1s t3s).
Proof.
  intros.
  rewrite - cat1s.
  by eapply bet_composition'; eauto.
Qed.

Lemma et_composition': forall s C es1 es2 t1s t2s t3s,
    e_typing s C es1 (Tf t1s t2s) ->
    e_typing s C es2 (Tf t2s t3s) ->
    e_typing s C (es1 ++ es2) (Tf t1s t3s).
Proof.
  move => s C es1 es2 t1s t2s t3s HType1 HType2.
  remember (rev es2) as es2'.
  assert (es2 = rev es2'); first by (rewrite Heqes2'; symmetry; apply revK).
  generalize dependent es1. generalize dependent es2.
  generalize dependent t1s. generalize dependent t2s.
  generalize dependent t3s.
  induction es2' => //=.
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1. destruct es2 => //=. rewrite cats0.
    apply et_to_bet in HType2. apply empty_typing in HType2. by subst.
  - by [].
  - move => t3s t2s t1s es2 HType2 H1 H2 es1 HType1.
    rewrite rev_cons in H2. rewrite -cats1 in H2.
    rewrite H2 in HType2.
    apply e_composition_typing in HType2.
    destruct HType2 as [ts [t1s' [t2s' [t3s' [H3 [H4 [H5 H6]]]]]]]. subst.
    rewrite catA. eapply ety_composition => //=.
    instantiate (1 := (ts ++ t3s')).
    eapply IHes2' => //.
    instantiate (1 := (ts ++ t1s')); first by apply ety_weakening.
    symmetry. by apply revK.
    by apply HType1.
    by apply ety_weakening.
Qed.

End composition_typing_proofs.

End Host.

