From Paco Require Import paco.

Require Import sflib.

Require Import Coq.Classes.RelationClasses.
Require Import ClassicalChoice PropExtensionality FunctionalExtensionality.

Require Import Ordinal iProp Lattice.

Set Implicit Arguments.
Set Primitive Projections.

Section LIBRARY.
  Lemma gpaco2_gpaco T0 T1 (gf: rel2 T0 T1 -> rel2 T0 T1)
        (gf_mon: monotone2 gf)
        clo r rg:
    gpaco2 gf clo (gpaco2 gf clo r rg) (gupaco2 gf clo (rg \2/ r)) <2= gpaco2 gf clo r rg.
  Proof.
    intros. apply gpaco2_unfold in PR; [|eauto].
    econstructor. apply rclo2_rclo. eapply rclo2_mon. apply PR. clear x0 x1 PR. intros.
    destruct PR; [|destruct H; apply IN].
    apply rclo2_base. left. pstep.
    eapply gf_mon. apply H. clear x0 x1 H. intros.
    cut (@gupaco2 _ _ gf clo (rg \2/ r) x0 x1).
    { intros. destruct H. eapply rclo2_mon. apply IN. intros.
      destruct PR0; [|right; apply H].
      left. eapply paco2_mon. apply H. intros. destruct PR0; apply H0.
    }
    apply gpaco2_gupaco; [eauto|]. eapply gupaco2_mon. apply PR. intros.
    destruct PR0; [apply H|].
    eapply gpaco2_mon; [apply H|right|left]; intros; apply PR0.
  Qed.
End LIBRARY.


Lemma dependent_choice A (B: A -> Type) (R: forall (a: A) (b: B a), Prop)
      (EXISTS: forall a, exists b, R a b)
  :
    exists (f: forall a, B a), forall a, R a (f a).
Proof.
  hexploit (@choice _ (@sigT _ B) (fun a s => exists (b: B a), s = existT _ a b /\ R a b)).
  { i. specialize (EXISTS x). des. esplits; eauto. }
  i. des.
  assert (feq: forall a : A, projT1 (f a) = a).
  { i. specialize (H a). des. rewrite H. auto. }
  exists (fun a => @eq_rect A (projT1 (f a)) B (projT2 (f a)) a (feq a)).
  i. specialize (H a). des.
  assert (eq_dep1 _ _ a b (projT1 (f a)) (projT2 (f a))).
  { eapply eq_dep_dep1.
    eapply eq_sigT_iff_eq_dep.
    remember (f a). inv H. auto. }
  inv H1. assert (h = feq a).
  { eapply proof_irrelevance. }
  subst. auto.
Qed.

Lemma forall_exists_commute A (B: A -> Type) (P: forall (a: A) (b: B a), Prop)
  :
    (forall (a: A), exists (b: B a), P a b)
    ->
    (exists (f: forall (a: A), B a), forall (a: A), P a (f a)).
Proof.
  i. eapply dependent_choice; eauto.
Qed.

Lemma forall_exists_commute_rev A (B: A -> Type) (P: forall (a: A) (b: B a), Prop)
  :
    (exists (f: forall (a: A), B a), forall (a: A), P a (f a)) ->
    (forall (a: A), exists (b: B a), P a b).
Proof.
  i. des. eauto.
Qed.

Lemma forall_exists_commute_eq A (B: A -> Type) (P: forall (a: A) (b: B a), Prop)
  :
    (forall (a: A), exists (b: B a), P a b)
    <->
    (exists (f: forall (a: A), B a), forall (a: A), P a (f a)).
Proof.
  split.
  - eapply forall_exists_commute; eauto.
  - eapply forall_exists_commute_rev; eauto.
Qed.

Lemma exists_forall_commute A (B: A -> Type) (P: forall (a: A) (b: B a), Prop)
  :
    (exists (a: A), forall (b: B a), P a b) ->
    (forall (f: forall (a: A), B a), exists (a: A), P a (f a)).
Proof.
  i. des. esplits; eauto.
Qed.

Lemma exists_forall_commute_rev A (B: A -> Type) (P: forall (a: A) (b: B a), Prop)
  :
    (forall (f: forall (a: A), B a), exists (a: A), P a (f a)) ->
    (exists (a: A), forall (b: B a), P a b).
Proof.
  i. eapply NNPP. ii. generalize (not_ex_all_not _ _ H0). i. clear H0.
  exploit (@dependent_choice A B (fun a b => ~ P a b)).
  { i. specialize (H1 a). eapply not_all_ex_not in H1; eauto. }
  i. des. specialize (H f). des. eapply x0; eauto.
Qed.

Lemma exists_forall_commute_eq A (B: A -> Type) (P: forall (a: A) (b: B a), Prop)
  :
    (exists (a: A), forall (b: B a), P a b) <->
    (forall (f: forall (a: A), B a), exists (a: A), P a (f a)).
Proof.
  split.
  - eapply exists_forall_commute; eauto.
  - eapply exists_forall_commute_rev; eauto.
Qed.

Variable E: Type.
Variable R: Type.

Module Step.
  Section Step.
    Variable state: Type.
    Variant sort: Type :=
    | angel X (k: X -> state)
    | demon X (k: X -> state)
    | ret (r: R)
    .

    Definition ub: sort := angel (@False_rect _).
    Definition nb: sort := demon (@False_rect _).

    Definition demon_set (S: state -> Prop) :=
      @demon (sigT S) (@projT1 _ _).

    Definition angel_set (S: state -> Prop) :=
      @angel (sigT S) (@projT1 _ _).

    Definition normal (s: state) := demon (@unit_rect (fun _ => state) s).
  End Step.
End Step.
Arguments Step.angel [_] X k.
Arguments Step.demon [_] X k.
Arguments Step.ret {_} r.
Arguments Step.ub {_}.
Arguments Step.nb {_}.
Arguments Step.normal [_] s.
Arguments Step.demon_set [_] S.
Arguments Step.angel_set [_] S.

Module Trace.
  Variant _t {t: Type} :=
  | _ret (r: R)
  | _cons (e: E) (tr: t)
  | _ub
  | _nb
  .

  CoInductive t: Type := mk { observe: @_t t; }.

  Definition ret (r: R) := mk (_ret r).
  Definition cons (e: E) (tr: t) := mk (_cons e tr).
  Definition ub := mk _ub.
  Definition nb := mk _nb.

  Definition is_nb (tr: t) := tr.(observe) = _nb.

  Variant _le' (le: t -> t -> Prop): @_t t -> @_t t -> Prop :=
  | le_ret r: _le' le (_ret r) (_ret r)
  | le_cons e tr0 tr1 (LE: le tr0 tr1): _le' le (_cons e tr0) (_cons e tr1)
  | le_ub tr: _le' le tr _ub
  | le_nb tr: _le' le _nb tr
  .
  Hint Constructors _le'.

  Definition _le := fun le tr0 tr1 => _le' le tr0.(observe) tr1.(observe).

  Lemma _le_mon: monotone2 _le.
  Proof.
    ii. unfold _le in *. inv IN; eauto.
  Qed.
  Hint Resolve _le_mon: paco.

  Definition le := paco2 _le bot2.
  Arguments le: clear implicits.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
  Proof.
    unfold Reflexive. pcofix CIH. i.
    pfold. unfold _le. destruct (observe x); econs. right. auto.
  Qed.
  Next Obligation.
  Proof.
    unfold Transitive. pcofix CIH. i. pfold. punfold H0. punfold H1.
    unfold _le. inv H0; inv H1; try rewrite <- H3 in *; pclearbot; clarify.
    econs. right. eauto.
  Qed.
End Trace.
Hint Resolve Trace._le_mon: paco.

Module Behavior.
  Definition t := Trace.t -> Prop.

  Definition le (bs0 bs1: t): Prop := bs0 <1= bs1.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation. ii. eauto. Qed.
  Next Obligation. ii. eauto. Qed.

  Global Program Instance le_Antisymmetric: Antisymmetric _ eq le.
  Next Obligation.
  Proof.
    extensionality tr. eapply propositional_extensionality. eauto.
  Qed.

  Definition top: t := fun tr => True.
  Definition bot: t := fun tr => False.
  Definition meet A (bss: A -> t): t :=
    fun tr => forall a, bss a tr.
  Definition join A (bss: A -> t): t :=
    fun tr => exists a, bss a tr.

  Definition cons (e: E) (bs: t): t :=
    fun tr =>
      match tr.(Trace.observe) with
      | Trace._cons e' tr' => e' = e /\ bs tr'
      (* | Trace._nb => True *)
      | _ => False
      end.

  Definition ret (r: R): t :=
    fun tr =>
      match tr.(Trace.observe) with
      | Trace._ret r' => r' = r
      (* | Trace._nb => True *)
      | _ => False
      end.

  Lemma join_meet A (B: A -> Type) (k: forall a (b: B a), t)
    :
      join (fun a => meet (k a)) =
      meet (fun (f: forall a, B a) => join (fun a => k a (f a))).
  Proof.
    eapply le_Antisymmetric.
    - unfold join, meet. ii. eapply exists_forall_commute in PR; eauto.
    - unfold join, meet. ii. eapply exists_forall_commute_rev; eauto.
  Qed.

  Lemma meet_join A (B: A -> Type) (k: forall a (b: B a), t)
    :
      meet (fun a => join (k a)) =
      join (fun (f: forall a, B a) => meet (fun a => k a (f a))).
  Proof.
    eapply le_Antisymmetric.
    - unfold join, meet. ii. eapply forall_exists_commute in PR; eauto.
    - unfold join, meet. ii. revert a. eapply forall_exists_commute_rev; eauto.
  Qed.

  Lemma meet_ret A r
        (INHABITED: inhabited A)
    :
      meet (fun a: A => ret r) = ret r.
  Proof.
    destruct INHABITED.
    eapply le_Antisymmetric.
    - ii. eapply PR; eauto.
    - ii. eauto.
  Qed.

  Lemma join_ret A r
        (INHABITED: inhabited A)
    :
      join (fun a: A => ret r) = ret r.
  Proof.
    destruct INHABITED. unfold join.
    eapply le_Antisymmetric.
    - ii. des. eauto.
    - ii. eauto.
  Qed.

  Lemma meet_cons A e k
        (INHABITED: inhabited A)
    :
      meet (fun a: A => cons e (k a)) = cons e (meet k).
  Proof.
    destruct INHABITED. unfold cons.
    eapply le_Antisymmetric.
    - ii. generalize (PR X).
      des_ifs. i. des. clarify. splits; auto.
      ii. specialize (PR a). ss. rewrite Heq in *. des; auto.
    - ii. des_ifs. des. clarify.
  Qed.

  Lemma join_cons A e k
        (INHABITED: inhabited A)
    :
      join (fun a: A => cons e (k a)) = cons e (join k).
  Proof.
    destruct INHABITED. unfold cons, join.
    eapply le_Antisymmetric.
    - ii. des. des_ifs. des; clarify. split; auto. esplits; eauto.
    - ii. des_ifs. des. clarify. esplits; eauto.
  Qed.

  Lemma meet_empty A k
        (INHABITED: ~ inhabited A)
    :
      @meet A k = top.
  Proof.
    eapply le_Antisymmetric.
    - ii. ss.
    - ii. exfalso. eauto.
  Qed.

  Lemma join_empty A k
        (INHABITED: ~ inhabited A)
    :
      @join A k = bot.
  Proof.
    unfold join. eapply le_Antisymmetric.
    - ii. des. exfalso. eauto.
    - ii. ss.
  Qed.

  Lemma meet_top A
    :
      meet (fun a: A => top) = top.
  Proof.
    eapply le_Antisymmetric; ii; ss.
  Qed.

  Lemma meet_bot A
        (INHABITED: inhabited A)
    :
      meet (fun a: A => bot) = bot.
  Proof.
    destruct INHABITED.
    eapply le_Antisymmetric.
    - ii. eapply PR; eauto.
    - ii. ss.
  Qed.

  Lemma join_top A
        (INHABITED: inhabited A)
    :
      join (fun a: A => top) = top.
  Proof.
    destruct INHABITED.
    eapply le_Antisymmetric.
    - ii. ss.
    - ii. exists X. eauto.
  Qed.

  Lemma join_bot A
    :
      join (fun a: A => bot) = bot.
  Proof.
    unfold join. eapply le_Antisymmetric.
    - ii. des. ss.
    - ii. ss.
  Qed.

  Lemma join_const A k
        (INHABITED: inhabited A)
    :
      join (fun _: A => k) = k.
  Proof.
    destruct INHABITED. unfold join.
    eapply le_Antisymmetric.
    - ii. des. eauto.
    - ii. esplits; eauto.
  Qed.

  Lemma meet_const A k
        (INHABITED: inhabited A)
    :
      meet (fun _: A => k) = k.
  Proof.
    destruct INHABITED.
    eapply le_Antisymmetric.
    - ii. eapply PR; eauto.
    - ii. eauto.
  Qed.

  Lemma cons_bot e
    :
      cons e bot = bot.
  Proof.
    eapply le_Antisymmetric.
    - ii. unfold cons in *. des_ifs. des; ss.
    - ss.
  Qed.

  Lemma meet_meet A (B: A -> Type) (k: forall a (b: B a), t)
    :
      meet (fun a => meet (k a)) =
      meet (fun (ab: sigT B) => let (a, b) := ab in k a b).
  Proof.
    eapply le_Antisymmetric.
    - ii. destruct a as [a b]. eapply PR; eauto.
    - ii. specialize (PR (existT _ a a0)). eauto.
  Qed.

  Lemma join_join A (B: A -> Type) (k: forall a (b: B a), t)
    :
      join (fun a => join (k a)) =
      join (fun (ab: sigT B) => let (a, b) := ab in k a b).
  Proof.
    unfold join. eapply le_Antisymmetric.
    - ii. des. exists (existT _ a a0). eauto.
    - ii. des. destruct a as [a b]. eauto.
  Qed.

  Lemma any_le_top bs
    :
      le bs top.
  Proof.
    ii. ss.
  Qed.

  Lemma bot_le_any bs
    :
      le bot bs.
  Proof.
    ii. ss.
  Qed.

  Lemma meet_infimum A (k: A -> t) a
    :
      le (meet k) (k a).
  Proof.
    ii. eauto.
  Qed.

  Lemma meet_spec A (k: A -> t) bs
        (LE: forall a, le bs (k a))
    :
      le bs (meet k).
  Proof.
    ii. eapply LE in PR; eauto.
  Qed.

  Lemma join_supremum A (k: A -> t) a
    :
      le (k a) (join k).
  Proof.
    unfold join. ii. eauto.
  Qed.

  Lemma join_spec A (k: A -> t) bs
        (LE: forall a, le (k a) bs)
    :
      le (join k) bs.
  Proof.
    unfold join. ii. des. eapply LE; eauto.
  Qed.

  Lemma cons_le_cons e bs0 bs1
        (LE: le bs0 bs1)
    :
      le (cons e bs0) (cons e bs1).
  Proof.
    unfold cons. ii. des_ifs. des; clarify. splits; eauto.
  Qed.

  Lemma meet_le_meet A0 A1 (k0: A0 -> t) (k1: A1 -> t)
        (SIM: forall a1, exists a0, le (k0 a0) (k1 a1))
    :
      le (meet k0) (meet k1).
  Proof.
    ii. specialize (SIM a). des. eauto.
  Qed.

  Lemma join_le_join A0 A1 (k0: A0 -> t) (k1: A1 -> t)
        (SIM: forall a0, exists a1, le (k0 a0) (k1 a1))
    :
      le (join k0) (join k1).
  Proof.
    unfold join. ii. des. specialize (SIM a). des. eauto.
  Qed.

  Section Interpret.
    Variable state: Type.
    Variable step: state -> E * Step.sort state.

    Definition _interpret (interpret: state -> t) (s: state): t :=
      let (e, next) := step s in
      cons e (match next with
              | Step.angel X k => meet (fun x => interpret (k x))
              | Step.demon X k => join (fun x => interpret (k x))
              | Step.ret r => ret r
              end).

    Lemma _interpret_mon: monotone2 _interpret.
    Proof.
      ii. unfold _interpret, cons in *.
      des_ifs; des; clarify; split; eauto.
      - ii. eapply LE. eapply IN0; eauto.
      - unfold join in *. des. eapply LE in IN0. esplits; eauto.
    Qed.
    Hint Resolve _interpret_mon: paco.

    Definition interpret: (state -> t) := paco2 _interpret bot2.

    Global Opaque join meet top bot cons ret.
  End Interpret.
End Behavior.
Hint Resolve Behavior._interpret_mon: paco.

Module BSimulationOld.
  Section BSimulation.
    Variable state_src state_tgt: Type.
    Variable step_src: state_src -> E * Step.sort state_src.
    Variable step_tgt: state_tgt -> E * Step.sort state_tgt.

    Definition _bsim (bsim: state_src -> state_tgt -> Prop)
               (st_src: state_src) (st_tgt: state_tgt): Prop :=
      let (e_src, next_src) := step_src st_src in
      let (e_tgt, next_tgt) := step_tgt st_tgt in
      e_src = e_tgt /\
      match next_src, next_tgt with
      | Step.angel X_src k_src, Step.angel X_tgt k_tgt =>
        forall x_src, exists x_tgt,
            bsim (k_src x_src) (k_tgt x_tgt)
      | Step.demon X_src k_src, Step.demon X_tgt k_tgt =>
        forall x_tgt, exists x_src,
            bsim (k_src x_src) (k_tgt x_tgt)
      | Step.ret r_src, Step.ret r_tgt => r_src = r_tgt
      | _, _ => False
      end.

    Lemma _bsim_mon: monotone2 _bsim.
    Proof.
      ii. unfold _bsim in *. des_ifs; des; clarify; splits; eauto.
      - i. specialize (IN0 x_src). des. eapply LE in IN0. eauto.
      - i. specialize (IN0 x_tgt). des. eapply LE in IN0. eauto.
    Qed.
    Hint Resolve _bsim_mon: paco.

    Definition bsim := paco2 _bsim bot2.
    Arguments bsim: clear implicits.

    Lemma adequacy:
      forall st_src st_tgt (SIM: bsim st_src st_tgt),
        Behavior.le (Behavior.interpret step_tgt st_tgt) (Behavior.interpret step_src st_src).
    Proof.
      pcofix CIH. i. pfold. punfold PR. punfold SIM.
      unfold _bsim at 1 in SIM.
      unfold Behavior._interpret at 1.
      unfold Behavior._interpret at 1 in PR.
      des_ifs; des; clarify.
      - eapply Behavior.cons_le_cons; eauto. ii.
        eapply Behavior.meet_le_meet; eauto.
        i. hexploit (SIM0 a1); eauto. i. des.
        exists x_tgt. ii. pclearbot. right. eauto.
      - eapply Behavior.cons_le_cons; eauto. ii.
        eapply Behavior.join_le_join; eauto.
        i. hexploit (SIM0 a0); eauto. i. des.
        exists x_src. ii. pclearbot. right. eauto.
    Qed.
  End BSimulation.
End BSimulationOld.

Module Compatible.
  Section Compatible.
    Variable state_src: Type.
    Variable step_src: state_src -> E * Step.sort state_src.

    Definition scompatible' sclo: Prop :=
      forall
        (r rg: state_src -> Behavior.t),
        sclo rg <2= gpaco2 (Behavior._interpret step_src) (cpn2 (Behavior._interpret step_src)) r rg.

    Structure scompatible sclo: Prop :=
      scompatible_intro {
          scompatible_mon: monotone2 sclo;
          scompatible_scompatible:> scompatible' sclo;
        }.
    Hint Constructors scompatible.

    Definition wcompatible' sclo: Prop :=
      forall
        (r rg: state_src -> Behavior.t),
        sclo r <2= gpaco2 (Behavior._interpret step_src) (cpn2 (Behavior._interpret step_src)) r rg.

    Structure wcompatible sclo: Prop :=
      wcompatible_intro {
          wcompatible_mon: monotone2 sclo;
          wcompatible_wcompatible:> wcompatible' sclo;
        }.
    Hint Constructors wcompatible.

    Lemma interpret_scompatible:
      scompatible (Behavior._interpret step_src).
    Proof.
      econs.
      { eapply Behavior._interpret_mon. }
      ii. gstep. eapply Behavior._interpret_mon; eauto.
      i. gbase. auto.
    Qed.

    Lemma id_wcompatible:
      wcompatible id.
    Proof.
      econs; eauto.
      ii. gbase. auto.
    Qed.

    Lemma scompatible_downward sclo0 sclo1
          (COMPAT: scompatible sclo0)
          (LE: sclo1 <3= sclo0)
          (MON: monotone2 sclo1)
      :
        scompatible sclo1.
    Proof.
      econs; eauto. ii. eapply LE in PR. eapply COMPAT; eauto.
    Qed.

    Lemma wcompatible_downward wclo0 wclo1
          (COMPAT: wcompatible wclo0)
          (LE: wclo1 <3= wclo0)
          (MON: monotone2 wclo1)
      :
        wcompatible wclo1.
    Proof.
      econs; eauto. ii. eapply LE in PR. eapply COMPAT; eauto.
    Qed.

    Lemma gpaco_wcompatible:
      wcompatible (gupaco2 (Behavior._interpret step_src) (cpn2 (Behavior._interpret step_src))).
    Proof.
      econs.
      { ii. eapply gpaco2_mon; eauto. }
      ii. eapply gpaco2_gpaco; eauto with paco.
      eapply gpaco2_mon; eauto.
      { i. gbase. auto. }
      { i. gbase. auto. }
    Qed.

    Lemma gpaco_scompatible:
      scompatible (gpaco2 (Behavior._interpret step_src) (cpn2 (Behavior._interpret step_src)) bot2).
    Proof.
      econs.
      { ii. eapply gpaco2_mon; eauto. }
      ii. eapply gpaco2_mon; eauto. ss.
    Qed.

    Definition gsclo :=
      fun sclo st_src tr =>
        exists _sclo,
          scompatible _sclo /\ _sclo sclo st_src tr.

    Lemma gsclo_scompatible
      :
        scompatible gsclo.
    Proof.
      unfold gsclo. econs.
      - ii. des. esplits; eauto. eapply IN; eauto.
      - ii. des. eapply PR; eauto.
    Qed.

    Lemma gsclo_greatest sclo
          (COMPAT: scompatible sclo)
      :
        sclo <3= gsclo.
    Proof.
      ii. unfold gsclo. esplits; eauto.
    Qed.

    Definition gwclo :=
      fun wclo st_src tr =>
        exists _wclo,
          wcompatible _wclo /\ _wclo wclo st_src tr.

    Lemma gwclo_wcompatible
      :
        wcompatible gwclo.
    Proof.
      unfold gwclo. econs.
      - ii. des. esplits; eauto. eapply IN; eauto.
      - ii. des. eapply PR; eauto.
    Qed.

    Lemma gwclo_greatest wclo
          (COMPAT: wcompatible wclo)
      :
        wclo <3= gwclo.
    Proof.
      ii. unfold gwclo. esplits; eauto.
    Qed.

    Lemma scompatible_wcompatible:
      scompatible <1= wcompatible.
    Proof.
      ii. econs.
      - eapply PR.
      - ii. eapply gpaco2_gpaco; eauto with paco. eapply PR.
        eapply PR; eauto. i. gbase. auto.
    Qed.

    Lemma wcompatible_compose wclo0 wclo1
          (COMPAT0: wcompatible wclo0)
          (COMPAT1: wcompatible wclo1)
      :
        wcompatible (compose wclo0 wclo1).
    Proof.
      econs.
      { eapply monotone2_compose.
        - eapply COMPAT0.
        - eapply COMPAT1.
      }
      ii. eapply gpaco2_gpaco; eauto with paco. unfold compose in PR.
      eapply COMPAT0; eauto. eapply COMPAT0; eauto.
      i. eapply COMPAT1; eauto.
    Qed.

    Lemma wcompatible_scompatible_compose wclo sclo
          (COMPAT0: wcompatible wclo)
          (COMPAT1: scompatible sclo)
      :
        scompatible (compose wclo sclo).
    Proof.
      econs.
      { eapply monotone2_compose.
        - eapply COMPAT0.
        - eapply COMPAT1.
      }
      ii. eapply gpaco2_gpaco; eauto with paco. unfold compose in PR.
      eapply COMPAT0; eauto. eapply COMPAT0; eauto.
      i. eapply COMPAT1; eauto.
    Qed.

    Lemma scompatible_wcompatible_compose sclo wclo
          (COMPAT0: scompatible sclo)
          (COMPAT1: wcompatible wclo)
      :
        scompatible (compose sclo wclo).
    Proof.
      econs.
      { eapply monotone2_compose.
        - eapply COMPAT0.
        - eapply COMPAT1.
      }
      ii. eapply gpaco2_gpaco; eauto with paco. unfold compose in PR.
      eapply COMPAT0; eauto. eapply COMPAT0; eauto.
      i. eapply COMPAT1; eauto. eapply COMPAT1; eauto.
    Qed.

    Lemma wcompatible_rclo wclo
          (COMPAT: wcompatible wclo)
      :
        wcompatible (rclo2 wclo).
    Proof.
      econs.
      { eapply rclo2_mon. }
      ii. induction PR.
      - gbase. auto.
      - eapply gpaco2_gpaco; eauto with paco. eapply COMPAT. eapply COMPAT; eauto.
    Qed.
  End Compatible.
End Compatible.

Module Diagram.
  Section Diagram.
    Variable state_src state_tgt: Type.
    Variable step_src: state_src -> E * Step.sort state_src.
    Variable step_tgt: state_tgt -> E * Step.sort state_tgt.

    Definition t :=
      (state_src -> state_tgt -> Prop) -> (state_src -> state_tgt -> Prop).

    Section Sim.
      Variable _sim: t.

      Variant _lift
              (lift: state_src -> Behavior.t): state_src -> Behavior.t :=
      | _lift_intro
          st_src st_tgt tr
          (DIAGRAM: _sim (fun st_src0 st_tgt0 =>
                            Behavior.interpret step_tgt st_tgt0 <1= lift st_src0)
                         st_src st_tgt)
          (TARGET: Behavior.interpret step_tgt st_tgt tr)
        :
          _lift lift st_src tr
      .
      Hint Constructors _lift.

      Structure scompatible_sim: Prop :=
        scompatible_sim_intro {
            scompatible_sim_mon: monotone2 _sim;
            scompatible_sim_scompatible: Compatible.scompatible step_src _lift;
          }.
      Hint Constructors scompatible_sim.
      Hint Resolve scompatible_sim_mon: paco.
      Hint Resolve scompatible_sim_scompatible: paco.

      Structure wcompatible_sim: Prop :=
        wcompatible_sim_intro {
            wcompatible_sim_mon: monotone2 _sim;
            wcompatible_sim_wcompatible: Compatible.wcompatible step_src _lift;
          }.
      Hint Constructors wcompatible_sim.
      Hint Resolve wcompatible_sim_mon: paco.
      Hint Resolve wcompatible_sim_wcompatible: paco.

      Hypothesis _sim_mon: monotone2 _sim.

      Lemma _lift_mon:
        monotone2 _lift.
      Proof.
        ii. inv IN. econs; eauto.
      Qed.

      Definition lift := paco2 _lift bot2.
    End Sim.
    Hint Resolve _lift_mon: paco.
    Arguments lift: clear implicits.

    Lemma _lift_compose _sim0 _sim1
          (MON0: monotone2 _sim0)
          (MON1: monotone2 _sim1)
      :
        _lift (compose _sim0 _sim1) <3=
        compose (_lift _sim0) (_lift _sim1).
    Proof.
      ii. inv PR. econs; eauto. unfold compose in *. eapply MON0; eauto.
      i. econs; eauto.
    Qed.

    Lemma _lift_rclo _sim
          (MON: monotone2 _sim)
      :
        _lift (rclo2 _sim) <3=
        rclo2 (_lift _sim).
    Proof.
      ii. inv PR. ginduction DIAGRAM.
      - i. econs 1; eauto.
      - i. econs 2.
        { i. eapply PR. }
        { econs; eauto. }
    Qed.

    Lemma _lift_sim_mon _sim0 _sim1
          (LE: _sim1 <3= _sim0)
      :
        _lift _sim1 <3= _lift _sim0.
    Proof.
      ii. inv PR. econs; eauto.
    Qed.

    Lemma scompatible_sim_downward ssim0 ssim1
          (COMPAT: scompatible_sim ssim0)
          (LE: ssim1 <3= ssim0)
          (MON: monotone2 ssim1)
      :
        scompatible_sim ssim1.
    Proof.
      econs; eauto.
      eapply Compatible.scompatible_downward.
      { eapply COMPAT. }
      { i. eapply _lift_sim_mon; eauto. }
      { eapply _lift_mon; eauto. }
    Qed.

    Lemma wcompatible_sim_downward wsim0 wsim1
          (COMPAT: wcompatible_sim wsim0)
          (LE: wsim1 <3= wsim0)
          (MON: monotone2 wsim1)
      :
        wcompatible_sim wsim1.
    Proof.
      econs; eauto.
      eapply Compatible.wcompatible_downward.
      { eapply COMPAT. }
      { i. eapply _lift_sim_mon; eauto. }
      { eapply _lift_mon; eauto. }
    Qed.

    Definition gssim: t :=
      fun sim st_src st_tgt =>
        exists (_sim: t),
          scompatible_sim _sim /\ _sim sim st_src st_tgt.

    Lemma gssim_scompatible_sim
      :
        scompatible_sim gssim.
    Proof.
      unfold gssim. econs.
      - ii. des. eapply IN in IN0; eauto.
      - econs.
        { ii. eapply _lift_mon; eauto.
          ii. des. esplits; eauto. eapply IN0; eauto. }
        ii. inv PR. des.
        eapply DIAGRAM; eauto. econs; eauto.
    Qed.

    Lemma gssim_greatest sim
          (COMPAT: scompatible_sim sim)
      :
        sim <3= gssim.
    Proof.
      ii. unfold gssim. esplits; eauto.
    Qed.

    Definition gwsim: t :=
      fun sim st_src st_tgt =>
        exists (_sim: t),
          wcompatible_sim _sim /\ _sim sim st_src st_tgt.

    Lemma gwsim_wcompatible_sim
      :
        wcompatible_sim gwsim.
    Proof.
      unfold gwsim. econs.
      - ii. des. eapply IN in IN0; eauto.
      - econs.
        { ii. eapply _lift_mon; eauto.
          ii. des. esplits; eauto. eapply IN0; eauto. }
        ii. inv PR. des.
        eapply DIAGRAM; eauto. econs; eauto.
    Qed.

    Lemma gwsim_greatest sim
          (COMPAT: wcompatible_sim sim)
      :
        sim <3= gwsim.
    Proof.
      ii. unfold gwsim. esplits; eauto.
    Qed.

    Lemma scompatible_sim_wcompatible:
      scompatible_sim <1= wcompatible_sim.
    Proof.
      ii. econs.
      - eapply PR.
      - eapply Compatible.scompatible_wcompatible; eauto. eapply PR.
    Qed.

    Lemma wcompatible_sim_compose wsim0 wsim1
          (COMPAT0: wcompatible_sim wsim0)
          (COMPAT1: wcompatible_sim wsim1)
      :
        wcompatible_sim (compose wsim0 wsim1).
    Proof.
      econs.
      { eapply monotone2_compose.
        - eapply COMPAT0.
        - eapply COMPAT1.
      }
      econs.
      { ii. inv IN. econs; eauto. unfold compose in *.
        eapply COMPAT0; eauto. i. eapply COMPAT1; eauto. }
      ii. eapply gpaco2_gpaco; eauto with paco. eapply _lift_compose in PR.
      2: { eapply COMPAT0. }
      2: { eapply COMPAT1. }
      unfold compose in *. eapply COMPAT0.
      eapply _lift_mon; eauto.
      { eapply COMPAT0. }
      i. eapply COMPAT1; eauto.
    Qed.

    Lemma wcompatible_scompatible_sim_compose wsim ssim
          (COMPAT0: wcompatible_sim wsim)
          (COMPAT1: scompatible_sim ssim)
      :
        scompatible_sim (compose wsim ssim).
    Proof.
      econs.
      { eapply monotone2_compose.
        - eapply COMPAT0.
        - eapply COMPAT1.
      }
      econs.
      { ii. inv IN. econs; eauto. unfold compose in *.
        eapply COMPAT0; eauto. i. eapply COMPAT1; eauto. }
      ii. eapply gpaco2_gpaco; eauto with paco. eapply _lift_compose in PR.
      2: { eapply COMPAT0. }
      2: { eapply COMPAT1. }
      unfold compose in *. eapply COMPAT0.
      eapply _lift_mon; eauto.
      { eapply COMPAT0. }
      i. eapply COMPAT1; eauto.
    Qed.

    Lemma scompatible_wcompatible_sim_compose ssim wsim
          (COMPAT0: scompatible_sim ssim)
          (COMPAT1: wcompatible_sim wsim)
      :
        scompatible_sim (compose ssim wsim).
    Proof.
      econs.
      { eapply monotone2_compose.
        - eapply COMPAT0.
        - eapply COMPAT1.
      }
      econs.
      { ii. inv IN. econs; eauto. unfold compose in *.
        eapply COMPAT0; eauto. i. eapply COMPAT1; eauto. }
      ii. eapply gpaco2_gpaco; eauto with paco. eapply _lift_compose in PR.
      2: { eapply COMPAT0. }
      2: { eapply COMPAT1. }
      unfold compose in *. eapply COMPAT0.
      eapply _lift_mon; eauto.
      { eapply COMPAT0. }
      i. eapply COMPAT1; eauto. eapply COMPAT1; eauto.
    Qed.

    Lemma wcompatible_sim_rclo wsim
          (COMPAT: wcompatible_sim wsim)
      :
        wcompatible_sim (rclo2 wsim).
    Proof.
      econs.
      { eapply rclo2_mon. }
      econs.
      { ii. eapply _lift_mon; eauto. eapply rclo2_mon. }
      ii. eapply _lift_rclo in PR.
      2: { eapply COMPAT. }
      ginduction PR.
      - i. gbase. auto.
      - i. eapply gpaco2_gpaco; eauto with paco. eapply COMPAT; eauto.
        eapply _lift_mon; eauto. eapply COMPAT.
    Qed.

    Lemma improve_scompatible
      :
        scompatible_sim (fun sim st_src st_tgt => Behavior.interpret step_tgt st_tgt <1= Behavior.interpret step_src st_src).
    Proof.
      econs; eauto. econs.
      { eapply _lift_mon; eauto. }
      ii. gfinal. right. inv PR.
      eapply DIAGRAM in TARGET.
      eapply paco2_mon; eauto. i. ss.
    Qed.

    Variable _sim: t.
    Hypothesis COMPATIBLE: scompatible_sim _sim.

    Let _sim_mon := COMPATIBLE.(scompatible_sim_mon).

    Definition sim := paco2 _sim bot2.
    Arguments sim: clear implicits.

    Lemma sim_adequacy:
      forall st_src st_tgt (SIM: sim st_src st_tgt),
        Behavior.le (Behavior.interpret step_tgt st_tgt) (Behavior.interpret step_src st_src).
    Proof.
      ginit.
      { i. eapply cpn2_wcompat. eapply Behavior._interpret_mon. }
      gcofix CIH. i.
      eapply COMPATIBLE. econs; eauto. punfold SIM. eapply _sim_mon.
      { eapply SIM. }
      i. pclearbot. eapply CIH; eauto.
    Qed.
  End Diagram.
End Diagram.

Module BSimulation.
  Section BSimulation.
    Variable state_src state_tgt: Type.
    Variable step_src: state_src -> E * Step.sort state_src.
    Variable step_tgt: state_tgt -> E * Step.sort state_tgt.

    Definition bsim (sim: state_src -> state_tgt -> Prop)
               (st_src: state_src) (st_tgt: state_tgt): Prop :=
      let (e_src, next_src) := step_src st_src in
      let (e_tgt, next_tgt) := step_tgt st_tgt in
      e_src = e_tgt /\
      match next_src, next_tgt with
      | Step.angel X_src k_src, Step.angel X_tgt k_tgt =>
        forall x_src, exists x_tgt,
            sim (k_src x_src) (k_tgt x_tgt)
      | Step.demon X_src k_src, Step.demon X_tgt k_tgt =>
        forall x_tgt, exists x_src,
            sim (k_src x_src) (k_tgt x_tgt)
      | Step.ret r_src, Step.ret r_tgt => r_src = r_tgt
      | _, _ => False
      end.

    Lemma bsim_mon: monotone2 bsim.
    Proof.
      ii. unfold bsim in *. des_ifs; des; clarify; splits; eauto.
      - i. specialize (IN0 x_src). des. eapply LE in IN0. eauto.
      - i. specialize (IN0 x_tgt). des. eapply LE in IN0. eauto.
    Qed.

    Lemma bsim_scompatible
      :
        Diagram.scompatible_sim step_src step_tgt bsim.
    Proof.
      econs.
      { eapply bsim_mon. }
      econs.
      { eapply Diagram._lift_mon. eapply bsim_mon. }
      gcofix CIH. i. inv PR. punfold TARGET. gstep.
      unfold bsim at 1 in DIAGRAM.
      unfold Behavior._interpret at 1.
      unfold Behavior._interpret at 1 in TARGET.
      des_ifs; des; clarify.
      - eapply Behavior.cons_le_cons; eauto. ii.
        eapply Behavior.meet_le_meet; eauto.
        i. hexploit (DIAGRAM0 a1); eauto. i. des.
        exists x_tgt. ii. pclearbot. gfinal. eauto.
      - eapply Behavior.cons_le_cons; eauto. ii.
        eapply Behavior.join_le_join; eauto.
        i. hexploit (DIAGRAM0 a0); eauto. i. des.
        exists x_src. ii. pclearbot. gfinal. eauto.
    Qed.
  End BSimulation.
End BSimulation.

Module TwoStep.
  Section TwoStep.
    Variable state_src state_tgt: Type.
    Variable step_src: state_src -> E * Step.sort state_src.
    Variable step_tgt: state_tgt -> E * Step.sort state_tgt.

    Definition twostepsim (sim: state_src -> state_tgt -> Prop)
               (st_src: state_src) (st_tgt: state_tgt): Prop :=
      let (e_tgt0, next_tgt0) := step_tgt st_tgt in
      match next_tgt0 with
      | Step.demon X_tgt0 k_tgt0 =>
        forall x_tgt0,
          let (e_tgt1, next_tgt1) := step_tgt (k_tgt0 x_tgt0) in
          match next_tgt1 with
          | Step.demon X_tgt1 k_tgt1 =>
            forall x_tgt1,
              let (e_src0, next_src0) := step_src st_src in
              match next_src0 with
              | Step.demon X_src0 k_src0 =>
                exists x_src0,
                let (e_src1, next_src1) := step_src (k_src0 x_src0) in
                match next_src1 with
                | Step.demon X_src1 k_src1 =>
                  exists x_src1,
                  e_tgt0 = e_src0 /\
                  e_tgt1 = e_src1 /\
                  sim (k_src1 x_src1) (k_tgt1 x_tgt1)
                | _ => False
                end
              | _ => False
              end
          | _ => False
          end
      | _ => False
      end.

    Lemma twostepsim_mon: monotone2 twostepsim.
    Proof.
      ii. unfold twostepsim in *. des_ifs; des; clarify; splits; eauto.
      specialize (IN x_tgt0). des_ifs. i.
      specialize (IN x_tgt1). des. exists x_src0. des_ifs. des. esplits; eauto.
    Qed.

    Lemma twostepsim_scompatible
      :
        Diagram.scompatible_sim step_src step_tgt twostepsim.
    Proof.
      econs.
      { eapply twostepsim_mon. }
      econs.
      { eapply Diagram._lift_mon. eapply twostepsim_mon. }
      gcofix CIH. i. inv PR. punfold TARGET. gstep.
      unfold twostepsim at 1 in DIAGRAM.
      unfold Behavior._interpret at 1 in TARGET.
      destruct (step_tgt st_tgt) as [e_tgt0 []] eqn:STEPTGT0; ss.
      destruct (classic (inhabited X)).
      - erewrite <- Behavior.join_cons in TARGET; eauto.
        destruct TARGET as [x_tgt0 TARGET]. specialize (DIAGRAM x_tgt0).
        eapply Behavior.cons_le_cons in TARGET.
        2: { ii. pclearbot. punfold PR. }
        unfold Behavior._interpret at 1 in TARGET.
        destruct (step_tgt (k x_tgt0)) as [e_tgt1 []] eqn:STEPTGT1; ss.
        destruct (classic (inhabited X0)).
        + erewrite <- Behavior.join_cons in TARGET; eauto.
          erewrite <- Behavior.join_cons in TARGET; eauto.
          destruct TARGET as [x_tgt1 TARGET]. specialize (DIAGRAM x_tgt1).
          unfold Behavior._interpret at 1.
          des_ifs. des. des_ifs. des. clarify.
          eapply Behavior.cons_le_cons; eauto. ii.
          exists x_src0. gstep.
          unfold Behavior._interpret at 1. rewrite Heq0.
          eapply Behavior.cons_le_cons; eauto.
          ii. pclearbot.
          exists x_src1. gfinal. eauto.
        + erewrite Behavior.join_empty in TARGET; eauto.
          erewrite Behavior.cons_bot in TARGET.
          erewrite Behavior.cons_bot in TARGET. ss.
      - erewrite Behavior.join_empty in TARGET; eauto.
        erewrite Behavior.cons_bot in TARGET. ss.
    Qed.
  End TwoStep.
End TwoStep.

Definition contractible (X: Type): Prop :=
  forall (x0 x1: X), x0 = x1.

Module FSimulation.
  Section FSimulation.
    Variable state_src state_tgt: Type.
    Variable step_src: state_src -> E * Step.sort state_src.
    Variable step_tgt: state_tgt -> E * Step.sort state_tgt.

    Definition fsim (sim: state_src -> state_tgt -> Prop)
               (st_src: state_src) (st_tgt: state_tgt): Prop :=
      let (e_src, next_src) := step_src st_src in
      let (e_tgt, next_tgt) := step_tgt st_tgt in
      e_src = e_tgt /\
      match next_src, next_tgt with
      | Step.angel X_src k_src, Step.angel X_tgt k_tgt =>
        forall x_src, exists x_tgt,
            sim (k_src x_src) (k_tgt x_tgt)
      | Step.demon X_src k_src, Step.demon X_tgt k_tgt =>
        inhabited X_src /\
        contractible X_tgt /\
        forall x_src, exists x_tgt,
            sim (k_src x_src) (k_tgt x_tgt)
      | Step.ret r_src, Step.ret r_tgt => r_src = r_tgt
      | _, _ => False
      end.

    Lemma fsim_mon: monotone2 fsim.
    Proof.
      ii. unfold fsim in *. des_ifs; des; clarify; splits; eauto.
      - i. specialize (IN0 x_src). des. eapply LE in IN0. eauto.
      - i. specialize (IN2 x_src). des. eapply LE in IN2. eauto.
    Qed.

    Lemma fsim_scompatible
      :
        Diagram.scompatible_sim step_src step_tgt fsim.
    Proof.
      eapply Diagram.scompatible_sim_downward.
      - eapply BSimulation.bsim_scompatible.
      - unfold fsim, BSimulation.bsim. i. des_ifs.
        des. clarify. splits; auto. i.
        destruct PR0. specialize (PR2 X1). des.
        specialize (PR1 x_tgt0 x_tgt). clarify. esplits; eauto.
      - eapply fsim_mon.
    Qed.
  End FSimulation.
End FSimulation.

Module Demo.
  Section Demo.
    Variable state_src state_tgt: Type.
    Variable step_src: state_src -> E * Step.sort state_src.
    Variable step_tgt: state_tgt -> E * Step.sort state_tgt.

    Variable st_src0 st_src1 st_src2 st_src3a st_src3b st_src4 st_src5: state_src.
    Variable st_tgt0 st_tgt1 st_tgt2 st_tgt3 st_tgt4 st_tgt5: state_tgt.

    Variable e0 e1 e2 e3 e4: E.

    Hypothesis STEPSRC0: step_src st_src0 = (e0, Step.angel nat (fun _ => st_src1)).
    Hypothesis STEPSRC1: step_src st_src1 = (e1, Step.demon unit (fun _ => st_src2)).
    Hypothesis STEPSRC2: step_src st_src2 = (e2, Step.demon bool (fun b => if b then st_src3a else st_src3b)).
    Hypothesis STEPSRC3A: step_src st_src3a = (e3, Step.demon unit (fun _ => st_src4)).
    Hypothesis STEPSRC3B: step_src st_src3b = (e3, Step.demon unit (fun _ => st_src0)).
    Hypothesis STEPSRC4: step_src st_src4 = (e4, Step.demon nat (fun _ => st_src5)).

    Hypothesis STEPTGT0: step_tgt st_tgt0 = (e0, Step.demon nat (fun _ => st_tgt1)).
    Hypothesis STEPTGT1: step_tgt st_tgt1 = (e1, Step.demon unit (fun _ => st_tgt2)).
    Hypothesis STEPTGT2: step_tgt st_tgt2 = (e2, Step.demon unit (fun _ => st_tgt3)).
    Hypothesis STEPTGT3: step_tgt st_tgt3 = (e3, Step.demon bool (fun b => if b then st_tgt0 else st_tgt4)).
    Hypothesis STEPTGT4: step_tgt st_tgt4 = (e4, Step.angel nat (fun _ => st_tgt5)).

    Hypothesis BEHAVIOR: Behavior.le (Behavior.interpret step_tgt st_tgt5) (Behavior.interpret step_src st_src5).

    Lemma refinement:
      Behavior.le (Behavior.interpret step_tgt st_tgt0) (Behavior.interpret step_src st_src0).
    Proof.
      ginit.
      { i. eapply cpn2_wcompat. eapply Behavior._interpret_mon. }
      gcofix CIH. i.
      (* manual refinement proof *)
      gstep. punfold PR.
      unfold Behavior._interpret at 1.
      unfold Behavior._interpret at 1 in PR.
      rewrite STEPSRC0. rewrite STEPTGT0 in PR.
      erewrite Behavior.meet_const.
      2: { econs. eapply 0. }
      erewrite Behavior.join_const in PR.
      2: { econs. eapply 0. }
      eapply Behavior.cons_le_cons; eauto. ii.
      (* upto backward simulation *)
      gpaco. eapply BSimulation.bsim_scompatible.
      pclearbot. econs; eauto.
      unfold BSimulation.bsim.
      rewrite STEPSRC1. rewrite STEPTGT1.
      splits; auto. i. exists x_tgt. i.
      (* upto two-step simulation *)
      gpaco. eapply TwoStep.twostepsim_scompatible.
      econs; eauto.
      unfold TwoStep.twostepsim.
      rewrite STEPTGT2. i. rewrite STEPTGT3. i.
      rewrite STEPSRC2. destruct x_tgt1.
      - exists false. rewrite STEPSRC3B. esplits; eauto. i.
        (* coinductive reasoning *)
        gbase. left. left. eapply CIH; eauto.
      - exists true. rewrite STEPSRC3A. esplits; eauto. i.
        (* go back to manual refinement proof *)
        gstep. punfold PR2.
        unfold Behavior._interpret at 1.
        unfold Behavior._interpret at 1 in PR2.
        erewrite STEPSRC4. erewrite STEPTGT4 in PR2.
        erewrite Behavior.join_const.
        2: { econs. eapply 0. }
        erewrite Behavior.meet_const in PR2.
        2: { econs. eapply 0. }
        eapply Behavior.cons_le_cons; eauto. ii.
        gfinal. right. pclearbot.
        eapply BEHAVIOR in PR3. eapply paco2_mon; eauto. ss.
    Qed.
  End Demo.
End Demo.
