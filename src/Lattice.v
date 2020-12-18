From Paco Require Import paco.

Require Import sflib.

Require Import Coq.Classes.RelationClasses Coq.Relations.Relation_Operators Coq.Classes.Morphisms ChoiceFacts. (* TODO: Use Morphisms *)
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.
Require Import Program.

Require Import Ordinal iProp.

Set Implicit Arguments.
Set Primitive Projections.

Section LATTICE.
  Variable X: Type.
  Let rel := X -> Prop.
  Let irel := X -> Ordinal.t -> Prop.

  Let le : rel -> rel -> Prop :=
    fun r0 r1 => forall x (IN: r0 x), r1 x.

  Variable F: rel -> rel -> rel.
  Hypothesis MON: forall rg0 rl0 rg1 rl1 (LEG: le rg0 rg1) (LEL: le rl0 rl1),
      le (F rg0 rl0) (F rg1 rl1).

  Definition ilift (ir: irel): irel :=
    fun x1 i =>
      F (fun x0 => iProp.future (ir x0) i) (fun x0 => iProp.next (ir x0) i) x1.

  Definition ilift_snd (r: rel) (ir: irel): irel :=
    fun x1 i => F (fun x0 => r x0) (fun x0 => iProp.next (ir x0) i) x1.

  Lemma ilift_mon: monotone2 ilift.
  Proof.
    ii. eapply MON; eauto.
    - ii. eapply iProp.future_mon; eauto. ii. auto.
    - ii. eapply iProp.next_mon; eauto. ii. auto.
  Qed.
  Hint Resolve ilift_mon: paco.

  Lemma ilift_snd_mon r: monotone2 (ilift_snd r).
  Proof.
    ii. eapply MON; eauto.
    { ii. auto. }
    { ii. eapply iProp.next_mon; eauto. ii. auto. }
  Qed.
  Hint Resolve ilift_snd_mon: paco.


  Definition closure: irel -> irel :=
    fun r x => iProp.closure (r x).

  Lemma closure_mon: monotone2 closure.
  Proof.
    ii. eapply iProp.closure_mon; eauto. ii. eauto.
  Qed.
  Hint Resolve closure_mon: paco.

  Lemma closure_compatible: compatible2 ilift closure.
  Proof.
    unfold closure. econs; eauto.
    { ii. eapply iProp.closure_mon; eauto. ii. auto. }
    { i. inv PR. des. eapply MON; [..|eauto].
      { ii. eapply iProp.closure_future. exists x. split; eauto. }
      { ii. eapply iProp.closure_next. exists x. split; eauto. }
    }
  Qed.

  Lemma igpaco_closed r rg:
    forall x, iProp.closed (gpaco2 ilift (cpn2 ilift) r rg x).
  Proof.
    ii. gclo. econs.
    { eapply closure_compatible. }
    { eexists. eauto. }
  Qed.

  Lemma ipaco_closed: forall x, iProp.closed (paco2 ilift bot2 x).
  Proof.
    i. eapply iProp.closure_eq_closed. revert x. ginit.
    { i. eapply cpn2_wcompat. eapply ilift_mon. }
    i. gclo. econs.
    { eapply closure_compatible. }
    eapply iProp.closure_mon; eauto. ii. gfinal. auto.
  Qed.

  Definition inaccessible (ir: irel) (k: Ordinal.t): Prop :=
    forall x i0 (IN: ir x i0),
    exists i1, ir x i1 /\ Ordinal.lt i1 k.

  (* excluded middle + choice needed *)
  Lemma inaccessible_ordinal_inaccessible
        k (INACCESSIBLE: Ordinal.inaccessible X Ordinal.O Ordinal.S k):
    forall (r: rel), inaccessible (paco2 (ilift_snd r) bot2) k.
  Proof.
    ii. revert i0 x IN.
    eapply (well_founded_induction Ordinal.lt_well_founded (fun i0 => forall x (IN: paco2 (ilift_snd r) bot2 x i0),
                                                                exists i1, (paco2 (ilift_snd r) bot2) x i1 /\ Ordinal.lt i1 k)).
    i. punfold IN. unfold ilift_snd at 1 in IN.

    hexploit (choice (fun (x1: X) (i: Ordinal.t) =>
                        Ordinal.lt i k /\
                        forall (IN: iProp.next (upaco2 (ilift_snd r) bot2 x1) x),                          iProp.next (upaco2 (ilift_snd r) bot2 x1) i)).
    { i. destruct (classic (iProp.next (upaco2 (ilift_snd r) bot2 x1) x)).
      { inv H0. des. pclearbot. hexploit H; eauto. i. des.
        exists (Ordinal.S i1). splits; auto.
        { eapply INACCESSIBLE. auto. }
        { i. exists i1. split; auto. eapply Ordinal.S_lt. }
      }
      { exists Ordinal.O. splits; auto.
        { eapply INACCESSIBLE. }
        { i. exfalso. eauto. }
      }
    }
    i. des. exists (Ordinal.join f). split.
    { pfold. eapply MON; eauto.
      { ii. auto. }
      { ii. eapply iProp.next_closed.
        { eapply H0. auto. }
        { eapply Ordinal.join_upperbound. }
      }
    }
    { eapply INACCESSIBLE. i. eapply H0. }
  Qed.

  Lemma kappa_inaccessible (r: rel):
    forall (r: rel), inaccessible (paco2 (ilift_snd r) bot2) (Ordinal.kappa X).
  Proof.
    eapply inaccessible_ordinal_inaccessible.
    eapply Ordinal.kappa_S_inaccessible.
    ii. eapply choice. auto.
  Qed.
End LATTICE.

Hint Resolve ilift_mon: paco.
Hint Resolve ilift_snd_mon: paco.

Section EQUIVALENCE.
  Variable X: Type.
  Let rel := X -> Prop.
  Let irel := X -> Ordinal.t -> Prop.

  Let le : rel -> rel -> Prop :=
    fun r0 r1 => forall x (IN: r0 x), r1 x.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    ii. eauto.
  Qed.
  Next Obligation.
  Proof.
    ii. eauto.
  Qed.

  Definition prefixpoint (f: rel -> rel) (r: rel) := le (f r) r.
  Definition postfixpoint (f: rel -> rel) (r: rel) := le r (f r).

  Definition mu (f: rel -> rel): rel :=
    fun x => forall (r: rel) (FIX: prefixpoint f r), r x.

  Lemma mu_least f r (FIX: prefixpoint f r):
    le (mu f) r.
  Proof.
    ii. eapply IN. auto.
  Qed.

  Lemma mu_fold f (MONOTONE: monotone1 f):
    le (f (mu f)) (mu f).
  Proof.
    ii. eapply FIX. eapply MONOTONE; eauto.
    i. eapply mu_least; eauto.
  Qed.

  Lemma mu_unfold f (MONOTONE: monotone1 f):
    le (mu f) (f (mu f)).
  Proof.
    ii. eapply IN. ii. eapply MONOTONE; eauto.
    i. ss. eapply mu_fold; eauto.
  Qed.

  Definition nu (f: rel -> rel): rel :=
    fun x => exists (r: rel), postfixpoint f r /\ r x.

  Lemma nu_greatest f r (FIX: postfixpoint f r):
    le r (nu f).
  Proof.
    ii. exists r. eauto.
  Qed.

  Lemma nu_unfold f (MONOTONE: monotone1 f):
    le (nu f) (f (nu f)).
  Proof.
    ii. unfold nu in IN. des. eapply IN in IN0. eapply MONOTONE; eauto.
    i. eapply nu_greatest; eauto.
  Qed.

  Lemma nu_fold f (MONOTONE: monotone1 f):
    le (f (nu f)) (nu f).
  Proof.
    ii. exists (f (nu f)). split; auto.
    ii. eapply MONOTONE; eauto. i. eapply nu_unfold; auto.
  Qed.

  Opaque mu nu.

  Variable F: rel -> rel -> rel.
  Hypothesis MON: forall rg0 rl0 rg1 rl1 (LEG: le rg0 rg1) (LEL: le rl0 rl1),
      le (F rg0 rl0) (F rg1 rl1).

  Variable k: Ordinal.t.
  Hypothesis INACCESSIBLE: forall (r: rel), inaccessible (paco2 (ilift_snd F r) bot2) k.

  Let MONFST: forall r, monotone1 (F r).
  Proof.
    ii. eapply MON; eauto. reflexivity.
  Qed.

  Let MONMU: monotone1 (fun r => mu (F r)).
  Proof.
    ii. eapply mu_least; eauto.
    ii. eapply mu_fold; eauto.
    eapply MON; eauto. reflexivity.
  Qed.

  Let ipaco_snd_mon: monotone1 (fun r x => exists i, paco2 (ilift_snd F r) bot2 x i).
  Proof.
    ii. des. exists i. revert x0 i IN. pcofix CIH. i.
    punfold IN. pfold. eapply MON; eauto.
    ii. eapply iProp.next_mon; eauto.
    ii. pclearbot. right. eauto.
  Qed.

  Let mu_equivalent r:
    forall x, mu (F r) x <-> (exists i, paco2 (ilift_snd F r) bot2 x i).
  Proof.
    i. split.
    { revert x. eapply mu_least. ii. exists k.
      pfold. eapply MON; eauto.
      { reflexivity. }
      ii. des. exploit INACCESSIBLE; eauto. i. des.
      exists i1. split; eauto.
    }
    { i. des. revert i x H.
      eapply (well_founded_induction Ordinal.lt_well_founded (fun i => forall x (IN: paco2 (ilift_snd F r) bot2 x i), mu (F r) x)).
      i. eapply mu_fold; auto. punfold IN.
      eapply MON; eauto.
      { reflexivity. }
      ii. inv IN0. des. pclearbot. eapply H; eauto.
    }
  Qed.

  Let nu_impl:
    forall x i (IN: paco2 (ilift_snd F (nu (fun r x => exists i, paco2 (ilift_snd F r) bot2 x i))) bot2 x i),
      paco2 (ilift F) bot2 x i.
  Proof.
    pcofix CIH. i. punfold IN. pfold.
    eapply MON; eauto.
    { ii. eapply nu_unfold in IN0; auto. des. exists i0.
      right. eapply CIH. eauto. }
    { ii. inv IN0. des. pclearbot. eapply CIH in H.
      exists x1. split; auto. }
  Qed.

  Let nu_equivalent:
    forall x, nu (fun r x => exists i, paco2 (ilift_snd F r) bot2 x i) x
              <-> exists i, paco2 (ilift F) bot2 x i.
  Proof.
    i. split.
    { i. eapply nu_unfold in H; auto. des.
      eapply nu_impl in H; eauto. }
    { revert x. eapply nu_greatest. ii. des. revert i x IN.
      eapply (well_founded_induction Ordinal.lt_well_founded (fun i => forall x (IN: paco2 (ilift F) bot2 x i), exists i0, paco2 (ilift_snd F (fun x => exists i1, paco2 (ilift F) bot2 x i1)) bot2 x i0)).
      i. exists k.
      pfold. punfold IN. unfold ilift_snd at 1. unfold ilift at 1 in IN.
      eapply MON; eauto.
      { ii. inv IN0. pclearbot. eauto. }
      { ii. inv IN0. des. pclearbot.
        hexploit H; eauto. i. des.
        eapply INACCESSIBLE in H2. des. exists i1. split; eauto. }
    }
  Qed.

  Theorem ipaco_munu:
    forall x, nu (fun r => mu (F r)) x <-> exists i, paco2 (ilift F) bot2 x i.
  Proof.
    i. etransitivity.
    2: { eapply nu_equivalent. }
    split; i.
    { revert x H. eapply nu_greatest. ii.
      eapply (mu_equivalent (nu (fun r : rel => mu (F r)))).
      eapply nu_unfold in IN; auto. }
    { revert x H. eapply nu_greatest. ii.
      eapply (mu_equivalent (nu (fun (r : rel) (x0 : X) => exists i : Ordinal.t, paco2 (ilift_snd F r) bot2 x0 i))).
      eapply nu_unfold in IN; auto. }
  Qed.

  Theorem ipaco_inaccessible:
    forall x i0 (IN: paco2 (ilift F) bot2 x i0),
    exists i1, paco2 (ilift F) bot2 x i1 /\ Ordinal.lt i1 k.
  Proof.
    i. hexploit (proj2 (nu_equivalent x)); eauto. i.
    eapply nu_unfold in H; auto. des.
    eapply INACCESSIBLE in H; eauto. des.
    eapply nu_impl in H. exists i1. split; auto.
  Qed.
End EQUIVALENCE.
