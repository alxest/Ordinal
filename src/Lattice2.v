From Paco Require Import paco.

Require Import sflib.

Require Import Coq.Classes.RelationClasses Coq.Relations.Relation_Operators Coq.Classes.Morphisms ChoiceFacts. (* TODO: Use Morphisms *)
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.
Require Import Program.

Require Import Ordinal iProp.

Set Implicit Arguments.
Set Primitive Projections.

Section LATTICE.
  Variable X0: Type.
  Variable X1: X0 -> Type.
  Let rel := forall (x0: X0) (x1: X1 x0), Prop.
  Let irel := forall (x0: X0) (x1: X1 x0), Ordinal.t -> Prop.

  Let le : rel -> rel -> Prop :=
    fun r0 r1 => forall x0 x1 (IN: r0 x0 x1), r1 x0 x1.

  Variable F: rel -> rel -> rel.
  Arguments F: clear implicits.

  Hypothesis MON: forall rg0 rl0 rg1 rl1 (LEG: le rg0 rg1) (LEL: le rl0 rl1),
      le (F rg0 rl0) (F rg1 rl1).

  Definition ilift2 (ir: irel): irel :=
    fun x0' x1' i =>
      F (fun x0 x1 => iProp.future (ir x0 x1) i) (fun x0 x1 => iProp.next (ir x0 x1) i) x0' x1'.

  Definition ilift2_snd (r: rel) (ir: irel): irel :=
    fun x0' x1' i => F (fun x0 x1 => r x0 x1) (fun x0 x1 => iProp.next (ir x0 x1) i) x0' x1'.

  Lemma ilift2_mon: monotone3 ilift2.
  Proof.
    ii. eapply MON; eauto.
    - ii. eapply iProp.future_mon; eauto. ii. auto.
    - ii. eapply iProp.next_mon; eauto. ii. auto.
  Qed.
  Hint Resolve ilift2_mon: paco.

  Lemma ilift2_snd_mon r: monotone3 (ilift2_snd r).
  Proof.
    ii. eapply MON; eauto.
    { ii. auto. }
    { ii. eapply iProp.next_mon; eauto. ii. auto. }
  Qed.
  Hint Resolve ilift2_snd_mon: paco.


  Definition closure: irel -> irel :=
    fun r x0 x1 => iProp.closure (r x0 x1).

  Lemma closure_mon: monotone3 closure.
  Proof.
    ii. eapply iProp.closure_mon; eauto. ii. eauto.
  Qed.
  Hint Resolve closure_mon: paco.

  Lemma closure_compatible: compatible3 ilift2 closure.
  Proof.
    unfold closure. econs; eauto.
    { ii. eapply iProp.closure_mon; eauto. ii. auto. }
    { i. inv PR. des. eapply MON; [..|eauto].
      { ii. eapply iProp.closure_future. exists x. split; eauto. }
      { ii. eapply iProp.closure_next. exists x. split; eauto. }
    }
  Qed.

  Lemma igpaco_closed r rg:
    forall x0 x1, iProp.closed (gpaco3 ilift2 (cpn3 ilift2) r rg x0 x1).
  Proof.
    ii. gclo. econs.
    { eapply closure_compatible. }
    { eexists. eauto. }
  Qed.

  Lemma ipaco_closed: forall x0 x1, iProp.closed (paco3 ilift2 bot3 x0 x1).
  Proof.
    i. eapply iProp.closure_eq_closed. revert x0 x1. ginit.
    { i. eapply cpn3_wcompat. eapply ilift2_mon. }
    i. gclo. econs.
    { eapply closure_compatible. }
    eapply iProp.closure_mon; eauto. ii. gfinal. auto.
  Qed.

  Definition inaccessible (ir: irel) (k: Ordinal.t): Prop :=
    forall x0 x1 i0 (IN: ir x0 x1 i0),
    exists i1, ir x0 x1 i1 /\ Ordinal.lt i1 k.

  Lemma inaccessible_larger ir k0 k1 (LE: Ordinal.le k0 k1)
        (INACCESSIBLE: inaccessible ir k0):
    inaccessible ir k1.
  Proof.
    ii. exploit INACCESSIBLE; eauto. i. des. esplits; eauto.
    eapply Ordinal.lt_le_lt; eauto.
  Qed.

  (* excluded middle + choice needed *)
  Lemma inaccessible_ordinal_inaccessible
        k (INACCESSIBLE: Ordinal.inaccessible (sigT X1) Ordinal.O Ordinal.S k):
    forall (r: rel), inaccessible (paco3 (ilift2_snd r) bot3) k.
  Proof.
    ii. revert i0 x0 x1 IN.
    eapply (well_founded_induction Ordinal.lt_well_founded (fun i0 => forall x0 x1 (IN: paco3 (ilift2_snd r) bot3 x0 x1 i0),
                                                                exists i1, (paco3 (ilift2_snd r) bot3) x0 x1 i1 /\ Ordinal.lt i1 k)).
    i. punfold IN. unfold ilift2_snd at 1 in IN.

    hexploit (choice (fun (x1: sigT X1) (i: Ordinal.t) =>
                        Ordinal.lt i k /\
                        forall (IN: iProp.next (upaco3 (ilift2_snd r) bot3 (projT1 x1) (projT2 x1)) x),                          iProp.next (upaco3 (ilift2_snd r) bot3 (projT1 x1) (projT2 x1)) i)).
    { i. destruct (classic (iProp.next (upaco3 (ilift2_snd r) bot3 (projT1 x2) (projT2 x2)) x)).
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
        { eapply (H0 (existT _ x2 x3)). auto. }
        { eapply Ordinal.join_upperbound. }
      }
    }
    { eapply INACCESSIBLE. i. eapply H0. }
  Qed.

  Lemma kappa_inaccessible (r: rel):
    forall (r: rel), inaccessible (paco3 (ilift2_snd r) bot3) (Ordinal.kappa (sigT X1)).
  Proof.
    eapply inaccessible_ordinal_inaccessible.
    eapply Ordinal.kappa_S_inaccessible.
    ii. eapply choice. auto.
  Qed.
End LATTICE.

Hint Resolve ilift2_mon: paco.
Hint Resolve ilift2_snd_mon: paco.
Arguments ilift2 [_] [_].
Arguments ilift2_snd [_] [_].
Arguments inaccessible [_] [_].

Section EQUIVALENCE.
  Variable X0: Type.
  Variable X1: X0 -> Type.
  Let rel := forall (x0: X0) (x1: X1 x0), Prop.
  Let irel := forall (x0: X0) (x1: X1 x0), Ordinal.t -> Prop.

  Let le : rel -> rel -> Prop :=
    fun r0 r1 => forall x0 x1 (IN: r0 x0 x1), r1 x0 x1.

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
    fun x0 x1 => forall (r: rel) (FIX: prefixpoint f r), r x0 x1.
  Arguments mu: clear implicits.

  Lemma mu_least f r (FIX: prefixpoint f r):
    le (mu f) r.
  Proof.
    ii. eapply IN. auto.
  Qed.

  Lemma mu_fold f (MONOTONE: monotone2 f):
    le (f (mu f)) (mu f).
  Proof.
    ii. eapply FIX. eapply MONOTONE; eauto.
    i. eapply mu_least; eauto.
  Qed.

  Lemma mu_unfold f (MONOTONE: monotone2 f):
    le (mu f) (f (mu f)).
  Proof.
    ii. eapply IN. ii. eapply MONOTONE; eauto.
    i. ss. eapply mu_fold; eauto.
  Qed.

  Definition nu (f: rel -> rel): rel :=
    fun x0 x1 => exists (r: rel), postfixpoint f r /\ r x0 x1.
  Arguments nu: clear implicits.

  Lemma nu_greatest f r (FIX: postfixpoint f r):
    le r (nu f).
  Proof.
    ii. exists r. eauto.
  Qed.

  Lemma nu_unfold f (MONOTONE: monotone2 f):
    le (nu f) (f (nu f)).
  Proof.
    ii. unfold nu in IN. des. eapply IN in IN0. eapply MONOTONE; eauto.
    i. eapply nu_greatest; eauto.
  Qed.

  Lemma nu_fold f (MONOTONE: monotone2 f):
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
  Hypothesis INACCESSIBLE: forall (r: rel), inaccessible (paco3 (ilift2_snd F r) bot3) k.

  Let MONFST: forall r, monotone2 (F r).
  Proof.
    ii. eapply MON; eauto. reflexivity.
  Qed.

  Let MONMU: monotone2 (fun r => mu (F r)).
  Proof.
    ii. eapply mu_least; eauto.
    ii. eapply mu_fold; eauto.
    eapply MON; eauto. reflexivity.
  Qed.

  Let ipaco_snd_mon: monotone2 (fun r x0 x1 => exists i, paco3 (ilift2_snd F r) bot3 x0 x1 i).
  Proof.
    ii. des. exists i. revert x0 x1 i IN. pcofix CIH. i.
    punfold IN. pfold. eapply MON; eauto.
    ii. eapply iProp.next_mon; eauto.
    ii. pclearbot. right. eauto.
  Qed.

  Let mu_equivalent r:
    forall x0 x1, mu (F r) x0 x1 <-> (exists i, paco3 (ilift2_snd F r) bot3 x0 x1 i).
  Proof.
    i. split.
    { revert x0 x1. eapply mu_least. ii. exists k.
      pfold. eapply MON; eauto.
      { reflexivity. }
      ii. des. exploit INACCESSIBLE; eauto. i. des.
      exists i1. split; eauto.
    }
    { i. des. revert i x0 x1 H.
      eapply (well_founded_induction Ordinal.lt_well_founded (fun i => forall x0 x1 (IN: paco3 (ilift2_snd F r) bot3 x0 x1 i), mu (F r) x0 x1)).
      i. eapply mu_fold; auto. punfold IN.
      eapply MON; eauto.
      { reflexivity. }
      ii. inv IN0. des. pclearbot. eapply H; eauto.
    }
  Qed.

  Let nu_impl:
    forall x0 x1 i (IN: paco3 (ilift2_snd F (nu (fun r x0 x1 => exists i, paco3 (ilift2_snd F r) bot3 x0 x1 i))) bot3 x0 x1 i),
      paco3 (ilift2 F) bot3 x0 x1 i.
  Proof.
    pcofix CIH. i. punfold IN. pfold.
    eapply MON; eauto.
    { ii. eapply nu_unfold in IN0; auto. des. exists i0.
      right. eapply CIH. eauto. }
    { ii. inv IN0. des. pclearbot. eapply CIH in H.
      exists x. split; auto. }
  Qed.

  Let nu_equivalent:
    forall x0 x1, nu (fun r x0 x1 => exists i, paco3 (ilift2_snd F r) bot3 x0 x1 i) x0 x1
                  <-> exists i, paco3 (ilift2 F) bot3 x0 x1 i.
  Proof.
    i. split.
    { i. eapply nu_unfold in H; auto. des.
      eapply nu_impl in H; eauto. }
    { revert x0 x1. eapply nu_greatest. ii. des. revert i x0 x1 IN.
      eapply (well_founded_induction Ordinal.lt_well_founded (fun i => forall x0 x1 (IN: paco3 (ilift2 F) bot3 x0 x1 i), exists i0, paco3 (ilift2_snd F (fun x0 x1 => exists i1, paco3 (ilift2 F) bot3 x0 x1 i1)) bot3 x0 x1 i0)).
      i. exists k.
      pfold. punfold IN. unfold ilift2_snd at 1. unfold ilift2 at 1 in IN.
      eapply MON; eauto.
      { ii. inv IN0. pclearbot. eauto. }
      { ii. inv IN0. des. pclearbot.
        hexploit H; eauto. i. des.
        eapply INACCESSIBLE in H2. des. exists i1. split; eauto. }
    }
  Qed.

  Theorem ipaco_munu:
    forall x0 x1, nu (fun r => mu (F r)) x0 x1 <-> exists i, paco3 (ilift2 F) bot3 x0 x1 i.
  Proof.
    i. etransitivity.
    2: { eapply nu_equivalent. }
    split; i.
    { revert x0 x1 H. eapply nu_greatest. ii.
      eapply (mu_equivalent (nu (fun r : rel => mu (F r)))).
      eapply nu_unfold in IN; auto. }
    { revert x0 x1 H. eapply nu_greatest. ii.
      eapply (mu_equivalent (nu (fun (r : rel) x0 x1 => exists i : Ordinal.t, paco3 (ilift2_snd F r) bot3 x0 x1 i))).
      eapply nu_unfold in IN; auto. }
  Qed.

  Theorem ipaco_inaccessible:
    forall x0 x1 i0 (IN: paco3 (ilift2 F) bot3 x0 x1 i0),
    exists i1, paco3 (ilift2 F) bot3 x0 x1 i1 /\ Ordinal.lt i1 k.
  Proof.
    i. hexploit (proj2 (@nu_equivalent x0 x1)); eauto. i.
    eapply nu_unfold in H; auto. des.
    eapply INACCESSIBLE in H; eauto. des.
    eapply nu_impl in H. exists i1. split; auto.
  Qed.
End EQUIVALENCE.
