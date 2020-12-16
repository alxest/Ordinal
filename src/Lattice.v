From Paco Require Import paco.

Require Import sflib.

Require Import Coq.Classes.RelationClasses Coq.Relations.Relation_Operators Coq.Classes.Morphisms ChoiceFacts. (* TODO: Use Morphisms *)
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.
Require Import Program.

Require Import Ordinal iProp.

Section LATTICE.
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

  Variable F: rel -> rel -> rel.
  Hypothesis MON: forall rg0 rl0 rg1 rl1 (LEG: le rg0 rg1) (LEL: le rl0 rl1),
      le (F rg0 rl0) (F rg1 rl1).

  Opaque iProp.future iProp.next.

  Inductive iF (o: Ordinal.t) (ir: irel): irel :=
  | iF_intro
      x1 i
      (REL: F (fun x0 => iProp.future (ir x0) i) (fun x0 => iProp.next_o (ir x0) o i) x1)
    :
      iF o ir x1 i
  .

  Lemma iF_mon o: monotone2 (iF o).
  Proof.
    ii. inv IN. econs. eapply MON; eauto.
    - ii. eapply iProp.future_mon; eauto. ii. auto.
    - ii. eapply iProp.next_o_mon; eauto. ii. auto.
  Qed.
  Hint Resolve iF_mon: paco.

  Definition munu (o: Ordinal.t) (x: X): Prop := exists i, paco2 (iF o) bot2 x i.

  Definition closure: irel -> irel :=
    fun r x => iProp.closure (r x).

  Lemma closure_mon: monotone2 closure.
  Proof.
    ii. eapply iProp.closure_mon; eauto. ii. eauto.
  Qed.
  Hint Resolve closure_mon: paco.

  Lemma closure_compatible o: compatible2 (cpn2 (iF o)) closure.
  Admitted.

  Lemma paco_index_decr o0 o1 (LE: Ordinal.le o0 o1) (r: irel)
        (CLOSED: forall x, iProp.closed (r x)):
    forall x, iProp.le (paco2 (iF o1) r x) (paco2 (iF o0) r x).
  Proof.
    pcofix CIH. i. punfold IN. inv IN. pfold. econs.
    eapply MON; eauto.
    { ii. eapply iProp.future_mon; eauto. ii. destruct IN0; eauto. }
    { ii. cut (iProp.next_o (upaco2 (iF o1) r x0) o0 o).
      { i. eapply iProp.next_o_mon; eauto. ii. destruct IN0; eauto. }
      { eapply iProp.next_o_decr; eauto. }
    }
  Qed.

  Lemma munu_o_eq o (LT: Ordinal.le (Ordinal.S Ordinal.O) o) x:
    (munu (Ordinal.S Ordinal.O) x) <-> (munu o x).
  Proof.
    unfold munu. split.
    { i. des. exists (Ordinal.mult o i). revert x i H.
      pcofix CIH. i. punfold H0. inv H0. pfold. econs.
      eapply MON; eauto.
      { ii. destruct IN. pclearbot. eapply CIH in H.
        eexists. right. eauto. }
      { ii. cut (next


        destruct IN.

        eauto.

        ii.

        eapply iProp.future eapply iProp.future


      unfol

      admit. }
    { i. unfold munu in *. des. eapply paco_index_decr in H; eauto. ii. ss. }
    {

      {


    <->


    (iProp.inhabited (paco2 (iF o) bot2 x)).

  Lemma paco_index_decr o0 o1 (LE: Ordinal.le o0 o1) (r: irel)
        (CLOSED: forall x, iProp.closed (r x)):
    forall x, iProp.le (paco2 (iF o1) r x) (paco2 (iF o0) r x).
  Proof.
    pcofix CIH. i. punfold IN. inv IN. pfold. econs.
    eapply MON; eauto.
    { ii. eapply iProp.future_mon; eauto. ii. destruct IN0.
      {

  Lemma paco_index_decr o0 o1 (LE: Ordinal.le o0 o1) (r: irel)
        (CLOSED: forall x, iProp.closed (r x)):
    forall x, iProp.le (paco2 (iF o1) r x) (paco2 (iF o0) r x).
  Proof.
    pcofix CIH. i. punfold IN. inv IN. pfold. econs.
    eapply MON; eauto.
    { ii. eapply iProp.future_mon; eauto. ii.


    i.


    forall x, iProp.closed (upaco2 (iF o) r x).
  Proof.
    i. eapply iProp.union_closed; eauto. eapply paco_index_closed. auto.
  Qed.


  Lemma munu_o_eq o (LT: Ordinal.le (Ordinal.S Ordinal.O) o):
    (exists

  Lemma paco_inhabited_kappa (r: irel) x
        (INHABITED: iProp.inhabited (paco2 iF r x)):
    iProp.lt (iProp.kappa X) (paco2 iF r x).
  Proof.
    eapply iProp.le_upper.
    2: { eapply iProp.next_closed. }


         eapply paco_index_closed.

    iProp.upper

    ii.



    <->
    (forall x, iProp.le ( paco2 iF r x i1.
  Proof.
    hexploit (choice (fun (x: X) (i1: Ordinal.t) =>
                        forall i0 (IN: paco2 iF r x i0),
                          paco2 iF r x i1)).
    { i. destruct (classic (exists i, paco2 iF r x i)).
      { des. eauto. }
      { exists Ordinal.O. i. exfalso. eauto. }
    }
    i. des. exists (Ordinal.join f). i. split; eauto.
    i. des. eapply H in H0.
    eapply paco_index_closed; eauto. eapply Ordinal.join_upperbound.
  Qed.

  Lemma paco_top_index_exists (r: irel):
    exists i1,
      forall x,
        (exists i0, paco2 iF r x i0) <-> paco2 iF r x i1.
  Proof.
    hexploit (choice (fun (x: X) (i1: Ordinal.t) =>
                        forall i0 (IN: paco2 iF r x i0),
                          paco2 iF r x i1)).
    { i. destruct (classic (exists i, paco2 iF r x i)).
      { des. eauto. }
      { exists Ordinal.O. i. exfalso. eauto. }
    }
    i. des. exists (Ordinal.join f). i. split; eauto.
    i. des. eapply H in H0.
    eapply paco_index_closed; eauto. eapply Ordinal.join_upperbound.
  Qed.


  Lemma paco_index_closed (r: irel)
        x i0 i1
        (LE: Ordinal.le i0 i1)
        (IN: paco2 iF r x i0):
    paco2 iF r x i1.
  Proof.
    revert x LE IN. pcofix CIH. i. punfold IN. inv IN.
    pfold. econs. eapply MON; eauto.
    { ii. eapply iProp.future_closed; eauto.
      eapply iProp.future_mon; eauto.
      ii. eapply upaco2_mon; eauto. }
    { ii. eapply iProp.next_closed; eauto.
      eapply iProp.next_mon; eauto.
      ii. eapply upaco2_mon; eauto. }
  Qed.

  Lemma upaco_index_closed (r: irel)
        (CLOSED: forall x i0 i1 (LE: Ordinal.le i0 i1) (IN: r x i0), r x i1)
        x i0 i1
        (LE: Ordinal.le i0 i1)
        (IN: upaco2 iF r x i0):
    upaco2 iF r x i1.
  Proof.
    destruct IN.
    { left. eapply paco_index_closed; eauto. }
    { right. eapply CLOSED; eauto. }
  Qed.

  Lemma paco_top_index_exists (r: irel):
    exists i1,
      forall x,
        (exists i0, paco2 iF r x i0) <-> paco2 iF r x i1.
  Proof.
    hexploit (choice (fun (x: X) (i1: Ordinal.t) =>
                        forall i0 (IN: paco2 iF r x i0),
                          paco2 iF r x i1)).
    { i. destruct (classic (exists i, paco2 iF r x i)).
      { des. eauto. }
      { exists Ordinal.O. i. exfalso. eauto. }
    }
    i. des. exists (Ordinal.join f). i. split; eauto.
    i. des. eapply H in H0.
    eapply paco_index_closed; eauto. eapply Ordinal.join_upperbound.
  Qed.

  Lemma upaco_top_index_exists (r: irel)
        (CLOSED: forall x i0 i1 (LE: Ordinal.le i0 i1) (IN: r x i0), r x i1):
    exists i1,
    forall x,
      (exists i0, upaco2 iF r x i0) <-> upaco2 iF r x i1.
  Proof.
    hexploit (choice (fun (x: X) (i1: Ordinal.t) =>
                        forall i0 (IN: upaco2 iF r x i0),
                          upaco2 iF r x i1)).
    { i. destruct (classic (exists i, upaco2 iF r x i)).
      { des. eauto. }
      { exists Ordinal.O. i. exfalso. eauto. }
    }
    i. des. exists (Ordinal.join f). i. split; eauto.
    i. des. eapply H in H0.
    eapply upaco_index_closed; eauto. eapply Ordinal.join_upperbound.
  Qed.

  Lemma upaco_bot_top_index_exists:
    exists i1,
      forall x,
        (exists i0, upaco2 iF bot2 x i0) <-> upaco2 iF bot2 x i1.
  Proof.
    eapply upaco_top_index_exists; eauto.
  Qed.

  Lemma munu_top_index_exists:
    exists i1,
      forall x, munu x <-> paco2 iF bot2 x i1.
  Proof.
    eapply paco_top_index_exists.
  Qed.

  Lemma munu_fixpoint: le munu (F munu munu) /\ le (F munu munu) munu.
  Proof.
    unfold munu. split.
    - ii. destruct IN as [i IN]. punfold IN. inv IN.
      eapply MON; eauto.
      { ii. ss. des. pclearbot. eauto. }
      { ii. ss. des. pclearbot. eauto. }
    - hexploit munu_top_index_exists. i. des.
      ii. exists (Ordinal.S i1). pfold. econs. eapply MON; eauto.
      { ii. ss. des. exists i. auto. }
      { ii. ss. des. exists i1. split.
        { eapply Ordinal.S_lt. }
        { left. eapply H; eauto. exists i; eauto. }
      }
  Qed.

  Lemma munu_least (r: rel) (LE: le (F munu r) r): le munu r.
  Proof.
    unfold munu in *. ii. des. revert i x IN.
    eapply (well_founded_induction (Ordinal.lt_well_founded) (fun i => forall x (IN: paco2 iF bot2 x i), r x)).
    i. punfold IN. inv IN. eapply LE.
    eapply MON; try apply REL; eauto.
    { ii. des. pclearbot. eauto. }
    { ii. ss. des. pclearbot. eauto. }
  Qed.


  Inductive iF (ir: irel): irel :=
  | iF_intro
      x1 i1
      (REL: F (fun x0 => exists i0, ir x0 i0) (fun x0 => exists i0, Ordinal.lt i0 i1 /\ ir x0 i0) x1)
    :
      iF ir x1 i1
  .

  Lemma iF_mon: monotone2 iF.
  Proof.
    ii. inv IN. econs. eapply MON; eauto.
    - ii. des. esplits; eauto.
    - ii. des. esplits; eauto.
  Qed.
  Hint Resolve iF_mon: paco.

  Definition munu (x: X): Prop := exists i, paco2 iF bot2 x i.

  Lemma paco_index_closed (r: irel)
        x i0 i1
        (LE: Ordinal.le i0 i1)
        (IN: paco2 iF r x i0):
    paco2 iF r x i1.
  Proof.
    revert x LE IN. pcofix CIH. i. punfold IN. inv IN.
    pfold. econs. eapply MON; eauto.
    { ii. des. esplits. eapply upaco2_mon; eauto. }
    { ii. ss. des. exists i2. splits.
      { eapply Ordinal.lt_le_lt; eauto. }
      { eapply upaco2_mon; eauto. }
    }
  Qed.

  Lemma upaco_index_closed (r: irel)
        (CLOSED: forall x i0 i1 (LE: Ordinal.le i0 i1) (IN: r x i0), r x i1)
        x i0 i1
        (LE: Ordinal.le i0 i1)
        (IN: upaco2 iF r x i0):
    upaco2 iF r x i1.
  Proof.
    destruct IN.
    { left. eapply paco_index_closed; eauto. }
    { right. eapply CLOSED; eauto. }
  Qed.

  Lemma upaco_bot_index_closed
        x i0 i1
        (LE: Ordinal.le i0 i1)
        (IN: upaco2 iF bot2 x i0):
    upaco2 iF bot2 x i1.
  Proof.
    eapply upaco_index_closed; eauto.
  Qed.

  Lemma paco_top_index_exists (r: irel):
    exists i1,
      forall x,
        (exists i0, paco2 iF r x i0) <-> paco2 iF r x i1.
  Proof.
    hexploit (choice (fun (x: X) (i1: Ordinal.t) =>
                        forall i0 (IN: paco2 iF r x i0),
                          paco2 iF r x i1)).
    { i. destruct (classic (exists i, paco2 iF r x i)).
      { des. eauto. }
      { exists Ordinal.O. i. exfalso. eauto. }
    }
    i. des. exists (Ordinal.join f). i. split; eauto.
    i. des. eapply H in H0.
    eapply paco_index_closed; eauto. eapply Ordinal.join_upperbound.
  Qed.

  Lemma upaco_top_index_exists (r: irel)
        (CLOSED: forall x i0 i1 (LE: Ordinal.le i0 i1) (IN: r x i0), r x i1):
    exists i1,
    forall x,
      (exists i0, upaco2 iF r x i0) <-> upaco2 iF r x i1.
  Proof.
    hexploit (choice (fun (x: X) (i1: Ordinal.t) =>
                        forall i0 (IN: upaco2 iF r x i0),
                          upaco2 iF r x i1)).
    { i. destruct (classic (exists i, upaco2 iF r x i)).
      { des. eauto. }
      { exists Ordinal.O. i. exfalso. eauto. }
    }
    i. des. exists (Ordinal.join f). i. split; eauto.
    i. des. eapply H in H0.
    eapply upaco_index_closed; eauto. eapply Ordinal.join_upperbound.
  Qed.

  Lemma upaco_bot_top_index_exists:
    exists i1,
      forall x,
        (exists i0, upaco2 iF bot2 x i0) <-> upaco2 iF bot2 x i1.
  Proof.
    eapply upaco_top_index_exists; eauto.
  Qed.

  Lemma munu_top_index_exists:
    exists i1,
      forall x, munu x <-> paco2 iF bot2 x i1.
  Proof.
    eapply paco_top_index_exists.
  Qed.

  Lemma munu_fixpoint: le munu (F munu munu) /\ le (F munu munu) munu.
  Proof.
    unfold munu. split.
    - ii. destruct IN as [i IN]. punfold IN. inv IN.
      eapply MON; eauto.
      { ii. ss. des. pclearbot. eauto. }
      { ii. ss. des. pclearbot. eauto. }
    - hexploit munu_top_index_exists. i. des.
      ii. exists (Ordinal.S i1). pfold. econs. eapply MON; eauto.
      { ii. ss. des. exists i. auto. }
      { ii. ss. des. exists i1. split.
        { eapply Ordinal.S_lt. }
        { left. eapply H; eauto. exists i; eauto. }
      }
  Qed.

  Lemma munu_least (r: rel) (LE: le (F munu r) r): le munu r.
  Proof.
    unfold munu in *. ii. des. revert i x IN.
    eapply (well_founded_induction (Ordinal.lt_well_founded) (fun i => forall x (IN: paco2 iF bot2 x i), r x)).
    i. punfold IN. inv IN. eapply LE.
    eapply MON; try apply REL; eauto.
    { ii. des. pclearbot. eauto. }
    { ii. ss. des. pclearbot. eauto. }
  Qed.

End LATTICE.
