Require Import List.

Lemma fold_fusion {V A B} (f: V -> A -> A) (g: V -> B -> B) (h: A -> B) (e: A) (xs: list V): (forall x y, h (f x y) = g x (h y)) -> h (fold_right f e xs) = fold_right g (h e) xs.
Proof.
  intro.
  induction xs.
  + unfold fold_right.
    reflexivity.
  + simpl.
    rewrite H.
    rewrite IHxs.
    reflexivity.
Qed.

Require Import Nat.

Fixpoint up (l: list nat): bool :=
  match l with
  | x1::xs1 => match xs1 with
      | x2::xs2 => (x1 <? x2) && (up xs1)
      | nil => true
      end
  | _ => true
  end
.

Definition ok x ys :=
  match ys with
  | y::ys => x <? y
  | nil => true
  end
.

Lemma filter_up_map_fusion x xss: filter up (map (cons x) xss) = map (cons x) (filter (ok x) (filter up xss)).
Proof.
  induction xss; [reflexivity |].
  simpl.
  rewrite IHxss.
  destruct a; [reflexivity |].
  set (up_a := up (n::a)).
  destruct up_a; simpl.
  + rewrite Bool.andb_true_r.
    set (x_lt_n := x <? n).
    destruct x_lt_n; reflexivity.
  + rewrite Bool.andb_false_r.
    reflexivity.
Qed.

Definition step x (xss: list (list nat)) := xss ++ map (cons x) xss.
Definition subseqs xs := fold_right step (nil::nil) xs.

Definition nstep x (xss: list (list nat)) := xss ++ map (cons x) (filter (ok x) xss).

Lemma fuse_subseqs_filter_up xs: filter up (subseqs xs) = fold_right nstep (nil::nil) xs.
Proof.
  unfold subseqs.
  apply (fold_fusion step nstep (filter up)).
  intros.
  unfold step.
  unfold nstep.
  rewrite filter_app.
  rewrite filter_up_map_fusion.
  reflexivity.
Qed.


