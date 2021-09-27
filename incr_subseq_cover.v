Require Import List.
Require Import Nat.
Require Import Orders.
Require Import OrdersFacts.
Require Import Program.

Module Type OrderedWithAdd (W: OrderedTypeFull').
  Parameter zero : W.t.
  Parameter zero_is_min : forall w, W.le zero w.
  Parameter add : W.t -> W.t -> W.t.
  Infix "+" := add.
  Infix "<=" := W.le.
  Parameter le_plus_trans : forall n m p : W.t, (n <= m) -> (n <= m + p).
  Parameter plus_le_compat : forall n m p : W.t, (n <= m) -> (n + p <= m + p).
End OrderedWithAdd.

Module Type Weight := OrderedTypeFull <+ OrderedWithAdd.

Module Ext (V: OrderedTypeFull) <: OrderedTypeFull.
  Inductive ext_val : Type :=
    | Bottom: ext_val
    | Val: forall (v: V.t), ext_val
    | Top: ext_val
  .
  Definition t := ext_val.

  Definition eq v1 v2 :=
    match v1, v2 with
    | Bottom, Bottom => True
    | Val v1, Val v2 => V.eq v1 v2
    | Top, Top => True
    | _, _ => False
    end.
  Infix "==" := eq (at level 70, no associativity).

  Lemma eq_equiv: Equivalence eq.
  Proof.
    split.
    + intro. destruct x; try constructor.
      apply V.eq_equiv.
    + intros x y.
      destruct x; destruct y; try constructor; try contradiction.
      apply V.eq_equiv.
    + intros x y z.
      destruct x; destruct y; destruct z; try constructor; try contradiction.
      apply V.eq_equiv.
  Qed.

  Definition lt v1 v2 :=
    match v2 with
    | Bottom => False
    | Val v2 =>
        match v1 with
        | Bottom => True
        | Val v1 => V.lt v1 v2
        | Top => False
        end
    | Top =>
        match v1 with
        | Top => False
        | _ => True
        end
    end.
  Infix "<" := lt.
  Notation "y > x" := (x < y) (only parsing).

  Lemma lt_strorder: StrictOrder lt.
  Proof.
    split.
    + intro.
      destruct x; intro; try contradiction.
      apply V.lt_strorder in H.
      contradiction.
    + intros x y z x_lt_y y_lt_z.
      destruct x; destruct y; destruct z; try contradiction; try constructor.
      revert x_lt_y y_lt_z.
      apply V.lt_strorder.
  Qed.

  Lemma lt_compat: Proper (eq ==> eq ==> iff) lt.
  Proof.
    intros x y.
    destruct x; destruct y ; try contradiction; try constructor;
    try (destruct x; destruct y ; try contradiction; try constructor).
    + apply V.lt_compat; apply V.eq_equiv; assumption.
    + apply V.lt_compat; assumption.
  Qed.

  Definition compare v1 v2 : comparison :=
    match v1, v2 with
    | Bottom, Bottom => Eq
    | Bottom, _ => Lt
    | _, Bottom => Gt
    | Top, Top => Eq
    | _, Top => Lt
    | Top, _ => Gt
    | Val v1, Val v2 => V.compare v1 v2
    end.

  Lemma compare_spec: forall x y, CompareSpec (x == y) (x < y) (x > y) (compare x y).
  Proof.
    destruct x; destruct y; try (constructor; constructor).
    apply V.compare_spec.
  Qed.

  Lemma eq_dec x y: {eq x y} + {~ eq x y}.
  Proof.
    destruct x; destruct y; try (left; constructor); try (right; intro; contradiction).
    apply V.eq_dec.
  Qed.

  Definition le v1 v2 :=
    match v1 with
    | Bottom => True
    | Val v1 =>
        match v2 with
        | Bottom => False
        | Val v2 => V.le v1 v2
        | Top => True
        end
    | Top =>
        match v2 with
        | Top => True
        | _ => False
        end
    end.
  Infix "<=" := le.

  Lemma le_lteq x y: (x <= y) <-> (x < y) \/ x == y.
  Proof.
    split; intro.
    + destruct x; destruct y; try (right; constructor); try (left; constructor); try contradiction.
      apply V.le_lteq. apply H.
    + destruct x; destruct y; try constructor; try (destruct H; contradiction).
      apply V.le_lteq. apply H.
  Qed.
End Ext.

Module IncrSubseq (V: OrderedTypeFull) (W: Weight).

Parameter weight_fn : V.t -> W.t.

Declare Scope value_scope.
Delimit Scope value_scope with value.
Open Scope value_scope.
Infix "<" := V.lt : value_scope.
Notation "x > y" := (y<x) (only parsing) : value_scope.
Infix "<=" := V.le : value_scope.
Notation "x >= y" := (y<=x) (only parsing) : value_scope.
Infix "==" := V.eq (at level 70, no associativity) : value_scope.
Module VFacts := OrderedTypeFullFacts V.

Declare Scope weight_scope.
Delimit Scope weight_scope with weight.
Open Scope weight_scope.
Infix "+" := W.add : weight_scope.
Infix "<" := W.lt : weight_scope.
Notation "x > y" := (y<x) (only parsing) : weight_scope.
Infix "<=" := W.le : weight_scope.
Notation "x >= y" := (y<=x) (only parsing) : weight_scope.
Infix "==" := W.eq (at level 70, no associativity) : weight_scope.
Module WFacts := OrderedTypeFullFacts W.

Module VExt := Ext V.
Import VExt(Bottom, Val, Top).
Module VExtFacts := OrderedTypeFullFacts VExt.
Infix "<" := VExt.lt.
Notation "x > y" := (y<x) (only parsing).
Infix "<=" := VExt.le.
Notation "x >= y" := (y<=x) (only parsing).
Infix "==" := VExt.eq (at level 70, no associativity).

Inductive incr_subseq : list V.t -> VExt.t -> W.t -> Type :=
  | ISEmpty : incr_subseq nil Bottom W.zero
  | ISSkip : forall h seq v w, incr_subseq seq v w -> incr_subseq (h::seq) v w
  | ISTake : forall h seq v w, incr_subseq seq v w -> v < Val h -> incr_subseq (h::seq) (Val h) (w + weight_fn h)
.

Arguments ISSkip h {seq} {v} {w}.
Arguments ISTake h {seq} {v} {w}.

Definition his {seq} {v} {w} (ss: incr_subseq seq v w) : Prop :=
  forall v' w' (ss': incr_subseq seq v' w'), (w >= w')%weight.

Definition dominates {seq} {v} {w} (ss1: incr_subseq seq v w) {v'} {w'} (ss2: incr_subseq seq v' w') :=
  v' <= v /\ (w >= w')%weight.
Infix ">>" := dominates (at level 70, no associativity).

Lemma empty_null_weight seq w (ss: incr_subseq seq Bottom w): w = W.zero.
Proof.
  induction seq.
  + inversion ss; reflexivity.
  + inversion ss.
    apply IHseq.
    apply X.
Qed.

Lemma incr_subseq_not_top seq : forall w (ss: incr_subseq seq Top w), False.
Proof.
  induction seq.
  + intros. inversion ss.
  + intros. inversion ss.
    apply (IHseq w X).
Qed.

Inductive cover (seq: list V.t): VExt.t -> W.t -> VExt.t -> Type :=
  | CEmpty : incr_subseq seq Bottom W.zero ->
      forall nv, (forall vu wu, incr_subseq seq vu wu -> vu < nv -> (wu == W.zero)%weight) ->
      cover seq Bottom W.zero nv
  | CCons : forall v w, incr_subseq seq (Val v) w ->
      forall v' w' (c': cover seq v' w' (Val v)), forall nv, Val v < nv ->
      (forall vu wu, incr_subseq seq vu wu -> vu < nv -> (wu <= w)%weight) ->
      cover seq (Val v) w nv
.

Arguments CEmpty {seq}.
Arguments CCons {seq} v {w}.

Definition last_subseq {seq v w nv} (cov: cover seq v w nv) : incr_subseq seq v w :=
  match cov with
  | CEmpty ess _ _ => ess
  | CCons _ ss _ _ _ _ _ _ => ss
  end.

Structure full_cover {seq} := FullCover
{
  fc_max_val: VExt.t;
  fc_max_weight: W.t;
  fc_cover: cover seq fc_max_val fc_max_weight Top;
}.
Arguments full_cover : clear implicits.
Arguments FullCover {seq fc_max_val fc_max_weight}.

Lemma cover_last_is_his {seq} (fcov: full_cover seq) : his (last_subseq (fc_cover fcov)).
Proof.
  destruct fcov; simpl.
  intros v w ss.
  inversion fc_cover0.
  + apply H in ss.
    apply W.le_lteq; right; assumption.
    destruct v; try constructor.
    apply incr_subseq_not_top in ss.
    contradiction.
  + apply H0 in ss; try assumption.
    destruct v; try constructor.
    apply incr_subseq_not_top in ss.
    contradiction.
Qed.

Inductive reverse_cover (seq: list V.t): VExt.t -> Type :=
  | RCEmpty: reverse_cover seq Top
  | RCCons: forall v w, incr_subseq seq (Val v) w -> forall nv, reverse_cover seq nv ->
      Val v < nv -> (forall vu wu, incr_subseq seq vu wu -> vu < nv -> (wu <= w)%weight) ->
      reverse_cover seq (Val v)
.

Arguments RCCons {seq}.

Inductive splitted_cover {seq split_val} := Splitted
{
  v_before : VExt.t;
  w_before : W.t;
  v_after : VExt.t;
  sc_before : cover seq v_before w_before v_after;
  sc_after : reverse_cover seq v_after;
  before_cond : v_before < Val split_val;
  after_cond : Val split_val <= v_after
}.
Arguments splitted_cover : clear implicits.
Arguments Splitted {seq split_val v_before w_before v_after}.

Program Fixpoint split_cover_fix split_val {seq v w nv} (cov: cover seq v w nv)
  (rc: reverse_cover seq nv) (split_lt_after: Val split_val <= nv) :
  splitted_cover seq split_val :=
  match cov with
  | CEmpty ess _ _ => Splitted cov rc _ _
  | CCons v ss v' w' cov' nv nv_bound Hdom =>
      match V.compare v split_val with
      | Lt => Splitted cov rc _ _
      | _ => split_cover_fix split_val cov' (RCCons _ _ ss nv rc nv_bound Hdom) _
      end
  end
.
Next Obligation.
  destruct (V.compare_spec v split_val); try discriminate.
  assumption.
Qed.
Next Obligation.
  destruct (V.compare_spec v split_val); try contradiction; rewrite V.le_lteq.
  + right. apply V.eq_equiv. assumption.
  + left. assumption.
Qed.

Program Definition split_cover split_val {seq} (cov: full_cover seq) :
  splitted_cover seq split_val :=
  split_cover_fix split_val (fc_cover cov) (RCEmpty seq) _.

Module VExtMinMax := GenericMinMax.GenericMinMax VExt.
Import VExtMinMax.
Module VExtMinMaxProp := GenericMinMax.MinMaxProperties VExt VExtMinMax.
Import VExtMinMaxProp.

Program Fixpoint cover_map_with_skip h {seq v w nv} (cov: cover seq v w nv) (v_lt_h: v < Val h) :
  cover (h::seq) v w (min (Val h) nv) :=
  match cov with
  | CEmpty ess _ Hdom => CEmpty (ISSkip h ess) _ _
  | CCons v ss v' w' cov' nv nv_bound Hdom =>
      CCons v (ISSkip h ss) v' w' (cover_map_with_skip h cov' _) (min (Val h) nv) _ _
  end.
Next Obligation.
  rewrite min_glb_lt_iff in H; destruct H.
  inversion X.
  + apply Hdom in X0; assumption.
  + rewrite <- H2 in *.
    apply VFacts.OrderTac.lt_irrefl in H.
    contradiction.
Qed.
Next Obligation.
  inversion cov'; try constructor.
  clear Heq_cov.
  revert H v_lt_h.
  apply V.lt_strorder.
Qed.
Next Obligation.
  compute.
  destruct (V.compare_spec h v); try constructor.
  + pose (Hcompat := V.lt_compat H (VFacts.OrderTac.eq_refl h)).
    rewrite <- Hcompat in v_lt_h.
    apply VFacts.OrderTac.lt_irrefl in v_lt_h.
    contradiction.
  + rewrite VFacts.lt_not_ge_iff in H.
    exfalso; apply H.
    rewrite V.le_lteq; left; assumption.
Qed.
Next Obligation.
  apply min_glb_lt; try assumption.
Qed.
Next Obligation.
  rewrite min_glb_lt_iff in H; destruct H.
  inversion X.
  + apply Hdom in X0; assumption.
  + rewrite <- H2 in *.
    apply VFacts.OrderTac.lt_irrefl in H.
    contradiction.
Qed.

Definition first_weight_gt {seq nv} (rc: reverse_cover seq nv) w :=
  match rc with
  | RCEmpty _ => True
  | RCCons _ w' _ _ _ _ _ => (w <= w')%weight
  end.

Program Fixpoint unstack_reverse_cover_with_skip h {seq v w nv}
  (cov: cover (h::seq) v w nv) (rc: reverse_cover seq nv) (h_le_v: Val h <= v)
  (rc_first_gt_w: first_weight_gt rc w) : full_cover (h::seq) :=
  match rc with
  | RCEmpty _ => FullCover cov
  | RCCons v' w' ss nv' rc' nv'_bound Hcov =>
      unstack_reverse_cover_with_skip h (CCons v' (ISSkip h ss) v w cov nv' nv'_bound _) rc' _ _
  end.
Next Obligation.
  destruct v; try contradiction; try inversion cov.
  rewrite <- Heq_rc in *; simpl in *.
  clear H0 H3 H4 v0 w0 nv Heq_rc rc.
  inversion X.
  + apply Hcov in X1; assumption.
  + rewrite <- H3 in *.
    clear H0 H4 H3 h0 seq0 vu.
    rewrite H5 in * |- *.
    apply H2 in X.
    * revert X rc_first_gt_w. apply WFacts.OrderTac.le_trans.
    * revert h_le_v H1. apply VFacts.OrderTac.le_lt_trans.
Qed.
Next Obligation.
  destruct v; try contradiction; try inversion cov.
  apply V.le_lteq; left.
  revert h_le_v H0; simpl.
  apply VFacts.OrderTac.le_lt_trans.
Qed.
Next Obligation.
  rewrite <- Heq_rc in *; simpl in *.
  clear Heq_rc rc.
  destruct rc'; try constructor.
  simpl.
  apply l0 in ss; try assumption.
  revert nv'_bound l.
  apply VExt.lt_strorder.
Qed.

Program Definition adapt_nv {seq v w nv} (cov: cover seq v w nv) new_nv (nv_eq: nv == new_nv) :
  cover seq v w new_nv :=
  match cov with
  | CEmpty ess nv Hcov => CEmpty ess new_nv _
  | CCons v ss v' w' cov' nv nv_bound Hdom => CCons v ss v' w' cov' new_nv _ _
  end.
Next Obligation.
  apply Hcov in X; try assumption.
  symmetry in nv_eq.
  apply (VExtFacts.OrderTac.lt_eq H nv_eq).
Qed.
Next Obligation.
  destruct nv0; destruct new_nv; try contradiction; try constructor.
  apply (VFacts.OrderTac.lt_eq nv_bound nv_eq).
Qed.
Next Obligation.
  apply Hdom in X; try assumption.
  symmetry in nv_eq.
  apply (VExtFacts.OrderTac.lt_eq H nv_eq).
Qed.

Program Fixpoint recompose_cover h {seq v w nv} (before: cover seq v w nv)
  {rv} (after: reverse_cover seq rv)
  (before_cond: v < Val h) (before_nv_cond: Val h <= nv) (after_cond: Val h <= rv)
  (dom_cond: forall vu wu, incr_subseq (h::seq) vu wu -> vu < rv -> (wu <= (w + weight_fn h))%weight):
  full_cover (h::seq) :=
  let before' := cover_map_with_skip h before before_cond in
  let new_subseq := ISTake h (last_subseq before) before_cond in
  match after with
  | RCEmpty _ => FullCover (CCons _ new_subseq _ _ before' Top _ _)
  | RCCons rv w' ss nv' after' nv'_bound Hcov =>
      match W.compare (w + weight_fn h) w' with
      | Lt =>
          match V.compare h rv with
          | Lt => unstack_reverse_cover_with_skip h (CCons _ new_subseq _ _ before' (Val rv) _ _) after _ _
          | _ => unstack_reverse_cover_with_skip h (CCons _ (ISSkip h ss) _ _ (adapt_nv before' _ _) nv' nv'_bound _) after' _ _
          end
      | _ => recompose_cover h before after' before_cond before_nv_cond _ _
      end
  end.
Next Obligation.
  destruct nv; try contradiction; try reflexivity.
  compute.
  destruct (V.compare_spec h v0); try reflexivity.
  rewrite VFacts.le_not_gt_iff in before_nv_cond.
  contradiction.
Qed.
Next Obligation.
  apply dom_cond in X; try assumption.
Qed.
Next Obligation.
  destruct nv; try contradiction; try reflexivity.
  compute.
  destruct (V.compare_spec h v0); try reflexivity.
  rewrite VFacts.le_not_gt_iff in before_nv_cond.
  contradiction.
Qed.
Next Obligation.
  apply VFacts.compare_lt_iff.
  symmetry; assumption.
Qed.
Next Obligation.
  apply dom_cond in X; try assumption.
Qed.
Next Obligation.
  apply VFacts.OrderTac.le_refl.
Qed.
Next Obligation.
  compute.
  rewrite <- Heq_after in * |- *.
  symmetry in Heq_anonymous0.
  rewrite WFacts.compare_lt_iff in Heq_anonymous0.
  rewrite W.le_lteq; left.
  assumption.
Qed.
Next Obligation.
  destruct (V.compare_spec h rv); try contradiction.
  + destruct nv; try contradiction; try assumption.
    compute.
    destruct (V.compare_spec h v0); try assumption.
    rewrite VFacts.le_not_gt_iff in before_nv_cond.
    contradiction.
  + rewrite VFacts.le_not_gt_iff in after_cond0.
    contradiction.
Qed.
Next Obligation.
  inversion X.
  + apply Hcov in X0; assumption.
  + rewrite <- H2 in *.
    symmetry in Heq_anonymous0.
    rewrite WFacts.compare_lt_iff in Heq_anonymous0.
    inversion before.
    * apply H6 in X0.
      - rewrite W.le_lteq; left.
        pose (Hz := W.zero_is_min w).
        apply (WFacts.OrderTac.eq_le X0) in Hz.
        apply (W.plus_le_compat _ _ (weight_fn h)) in Hz.
        apply (WFacts.OrderTac.le_lt_trans Hz Heq_anonymous0).
      - destruct nv; destruct v0; try contradiction; try constructor.
        simpl in H5 |- *.
        apply (VFacts.OrderTac.lt_le_trans H5 before_nv_cond).
    * apply H7 in X0.
      - rewrite W.le_lteq; left.
        apply (W.plus_le_compat _ _ (weight_fn h)) in X0.
        apply (WFacts.OrderTac.le_lt_trans X0 Heq_anonymous0).
      - destruct nv; destruct v0; try contradiction; try constructor.
        simpl in * |- *.
        apply (VFacts.OrderTac.lt_le_trans H5 before_nv_cond).
Qed.
Next Obligation.
  destruct after'; try constructor.
  simpl.
  clear Heq_after after.
  apply l0 in ss; try assumption.
  transitivity (Val v0); assumption.
Qed.
Next Obligation.
  destruct nv'; try contradiction; try constructor.
  simpl in nv'_bound.
  transitivity rv; try assumption.
  rewrite V.le_lteq; left; assumption.
Qed.
Next Obligation.
  apply not_eq_sym in H.
  rewrite WFacts.compare_ge_iff in H.
  inversion X.
  + apply Hcov in X0; try transitivity w'; assumption.
  + apply W.plus_le_compat.
    inversion before.
    * apply H6 in X0; try (rewrite W.le_lteq; right; assumption).
      destruct nv; destruct v0; try contradiction; try constructor.
      simpl in * |- *.
      apply (VFacts.OrderTac.lt_le_trans H5 before_nv_cond).
    * apply H7 in X0; try assumption.
      destruct nv; destruct v0; try contradiction; try constructor.
      simpl in * |- *.
      apply (VFacts.OrderTac.lt_le_trans H5 before_nv_cond).
Qed.

Program Definition step h {seq} (fcov: full_cover seq) : full_cover (h::seq) :=
  let sc := split_cover h fcov in
  recompose_cover h (sc_before sc) (sc_after sc) (before_cond sc) (after_cond sc) (after_cond sc) _
.
Next Obligation.
  destruct (split_cover h fcov); simpl in *.
  inversion X.
  + inversion sc_before0.
    * apply H4 in X0; try assumption.
      apply W.le_plus_trans.
      rewrite W.le_lteq; right; assumption.
    * apply H5 in X0; try assumption.
      apply W.le_plus_trans.
      assumption.
  + apply W.plus_le_compat.
    inversion sc_before0.
    * apply W.le_lteq; right.
      apply H5 in X0; try assumption.
      destruct v_after0; destruct v; try contradiction; try constructor.
      simpl in * |- *.
      apply (VFacts.OrderTac.lt_le_trans H4 after_cond0).
    * apply H6 in X0; try assumption.
      destruct v_after0; destruct v; try contradiction; try constructor.
      simpl in * |- *.
      apply (VFacts.OrderTac.lt_le_trans H4 after_cond0).
Qed.

Program Definition empty_cover := CEmpty ISEmpty Top _.
Next Obligation.
  inversion X.
  reflexivity.
Qed.

Fixpoint build_full_cover seq : full_cover seq :=
  match seq with
  | nil => FullCover empty_cover
  | h::t => step h (build_full_cover t)
  end.

Definition compute_his seq := last_subseq (fc_cover (build_full_cover seq)).

Lemma his_is_his seq : his (compute_his seq).
Proof.
  apply cover_last_is_his.
Qed.

End IncrSubseq.
