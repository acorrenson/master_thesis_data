From Coq Require Import ZArith List String Logic.FunctionalExtensionality Program.Equality.
Import ListNotations.

(** * Formalization of a symbolic bug finder for the language BUG *)

(** ** Syntaxe of BUG *)

Definition ident := string.

(** Expressions *)
Inductive aexpr : Type :=
  | Var : ident -> aexpr
  | Cst : Z -> aexpr
  | Add : aexpr -> aexpr -> aexpr
  | Sub : aexpr -> aexpr -> aexpr.

Inductive bexpr : Type :=
  | Bcst  : bool -> bexpr
  | Ble   : aexpr -> aexpr -> bexpr
  | Beq   : aexpr -> aexpr -> bexpr
  | Bnot  : bexpr -> bexpr
  | Band  : bexpr -> bexpr -> bexpr.

(** Commands *)
Inductive prog : Type :=
  | Skip  : prog
  | Ite   : bexpr -> prog -> prog -> prog
  | Seq   : prog -> prog -> prog
  | Asg   : string -> aexpr -> prog
  | Err   : prog
  | Loop  : bexpr -> prog -> prog.

Definition Assert c := Ite c Skip Err.

(** ** Concrete semantics of BUG *)

Module Concr.

(** Concrete memories *)
Definition store := ident -> Z.

(** Concrete states *)
Definition state : Type := store * prog.

(** Semantics of arithmetic expressions *)
Fixpoint aeval (s : store) (e : aexpr) : Z :=
  match e with
  | Var x => s x
  | Cst c => c
  | Add e1 e2 => aeval s e1 + aeval s e2
  | Sub e1 e2 => aeval s e1 - aeval s e2
  end.

(** Semantics of boolean expressions *)
Fixpoint beval (s : store) (e : bexpr) : bool :=
  match e with
  | Bcst b      => b
  | Ble e1 e2   => (aeval s e1 <=? aeval s e2)%Z
  | Beq e1 e2   => (aeval s e1 =? aeval s e2)%Z
  | Band e1 e2  => beval s e1 && beval s e2
  | Bnot e      => negb (beval s e)
  end.

(** Updating a store *)
Definition update (s : store) (x : ident) (v : Z) : store :=
  fun y => if (y =? x)%string then v else s y.

(** Small-step semantics *)
Inductive step : state -> state -> Prop :=
  | step_Aff s x e ve :
    aeval s e = ve -> step (s, Asg x e) (update s x ve, Skip)
  | step_Seq s1 s2 c1 c2 c3 :
    step (s1, c1) (s2, c2) -> step (s1, Seq c1 c3) (s2, Seq c2 c3)
  | step_Seq_Skip s c :
    step (s, Seq Skip c) (s, c)
  | step_Ite_true s e c1 c2 :
    beval s e = true -> step (s, Ite e c1 c2) (s, c1)
  | step_Ite_false s e c1 c2 :
    beval s e = false -> step (s, Ite e c1 c2) (s, c2)
  | step_Loop_true s e c :
    beval s e = true -> step (s, Loop e c) (s, Seq c (Loop e c))
  | step_Loop_false s e c :
    beval s e = false -> step (s, Loop e c) (s, Skip).

(** Reflexive transitive closure of [step] *)
Inductive steps : state -> state -> Prop :=
  | steps_refl s :
    steps s s
  | steps_step s1 s2 s3 :
    steps s1 s2 -> step s2 s3 -> steps s1 s3.

Definition progress '((env, p) : state) :=
  p = Skip \/ exists s, step (env, p) s.

Definition stuck '((env, p) : state) :=
  ~progress (env, p).

(** [Skip] can progress *)
Theorem progress_Skip:
  forall env, progress (env, Skip).
Proof.
  now left.
Qed.

(** [Ite] can progress *)
Theorem progress_Ite:
  forall env b p1 p2, progress (env, Ite b p1 p2).
Proof.
  intros *. right.
  destruct (beval env b) eqn:Hsat.
  * exists (env, p1). now econstructor.
  * exists (env, p2). now econstructor.
Qed.

(** [Asg] can progress *)
Theorem progress_Asg:
  forall env x e, progress (env, Asg x e).
Proof.
  intros *. right.
  repeat econstructor.
Qed.

(** [Seq] can progress *)
Theorem progress_Seq:
  forall env p1 p2, progress (env, p1) -> progress (env, Seq p1 p2).
Proof.
  intros * [-> | ((s' & p') & H)].
  - right. exists (env, p2). econstructor.
  - right. exists (s', (Seq p' p2)). now econstructor.
Qed.

(** [Loop] can progress *)
Theorem progress_Loop:
  forall env b p, progress (env, Loop b p).
Proof.
  intros *. right.
  destruct (beval env b) eqn:Hsat.
  - exists (env, Seq p (Loop b p)). now repeat econstructor.
  - exists (env, Skip). now repeat econstructor.
Qed.

(** If a sequence [Seq p1 p2] can't progress, then [p1] can't progress *)
Theorem stuck_seq:
  forall s p1 p2, stuck (s, Seq p1 p2) -> stuck (s, p1).
Proof.
  intros * H Hcontr.
  apply H, progress_Seq, Hcontr.
Qed.

(** What it means for a program to "go wrong" from a given memory *)
Definition goes_wrong (p : prog) (env1 : store):=
  exists s, steps (env1, p) s /\ stuck s.

End Concr.


Module Oracle.

Inductive NextErr : prog -> Prop :=
  | NextErr_Err : NextErr Err
  | NextErr_Seq p1 p2 : NextErr p1 -> NextErr (Seq p1 p2).

Fixpoint next_is_error (p : prog) :=
  match p with
  | Err => true
  | Seq p _ => next_is_error p
  | _ => false
  end.

Lemma next_is_error_correct:
  forall p, NextErr p <-> next_is_error p = true.
Proof.
  intros p. split.
  - induction 1; auto.
  - intros H. induction p; try easy; simpl in *.
    constructor; auto.
    constructor.
Qed.

Lemma NextErr_stuck:
  forall env p, Concr.stuck (env, p) <-> NextErr p.
Proof.
  intros env p. split.
  - intros Hstuck.
    induction p.
  + destruct Hstuck.
    apply Concr.progress_Skip.
  + destruct Hstuck.
    apply Concr.progress_Ite.
  + apply Concr.stuck_seq in Hstuck.
    constructor; auto.
  + destruct Hstuck.
    apply Concr.progress_Asg.
  + constructor.
  + destruct Hstuck.
    apply Concr.progress_Loop.
  - induction 1.
  + intros [[=]| [s Hs]]; try easy.
  + intros [[=]| [s Hs]]; try easy.
    inversion Hs; subst.
    apply IHNextErr. right. eexists _; eauto.
    apply IHNextErr. now left.
Qed.

Lemma next_is_error_stuck:
  forall env p, Concr.stuck (env, p) <-> next_is_error p = true.
Proof.
  intros.
  rewrite <- next_is_error_correct.
  apply NextErr_stuck.
Qed.

End Oracle.

(** ** Symbolic semantics of BUG *)

Module Symb.

(** Symbolic memories *)
Definition store :=
  ident -> aexpr.

(** Symbolic states *)
Definition state : Type := bexpr * store * prog.

(** Initial symbolic memory assigning to each variable its own name *)
Definition id : store := fun x => Var x.

(** Initial symbolic state *)
Definition init p : state := (Bcst true, id, p).

Definition path '((path, _, _) : state) := path.

(** Update a symbolic store *)
Definition update (s : store) (x : ident) (e : aexpr) : store :=
  fun y => if (y =? x)%string then e else s y.

(** Symbolic evaluation of arithmetic expressions *)
Fixpoint aeval (s : store) (e : aexpr) : aexpr :=
  match e with
  | Var x => s x
  | Cst c => e
  | Add e1 e2 => Add (aeval s e1) (aeval s e2)
  | Sub e1 e2 => Sub (aeval s e1) (aeval s e2)
  end.

(** Symbolic evaluation of boolean expressions *)
Fixpoint beval (s : store) (e : bexpr) : bexpr :=
  match e with
  | Bcst b      => e
  | Ble e1 e2   => Ble (aeval s e1) (aeval s e2)
  | Beq e1 e2   => Beq (aeval s e1) (aeval s e2)
  | Band e1 e2  => Band (beval s e1) (beval s e2)
  | Bnot e      => Bnot (beval s e)
  end.


(** Small-step symbolic semantics *)
Inductive step : state -> state -> Prop :=
  | step_Aff s π x e ve :
    aeval s e = ve -> step (π, s, Asg x e) (π, update s x ve, Skip)
  | step_Seq π1 π2 s1 s2 c1 c2 c3 :
    step (π1, s1, c1) (π2, s2, c2) -> step (π1, s1, Seq c1 c3) (π2, s2, Seq c2 c3)
  | step_Seq_Skip s c :
    step (s, Seq Skip c) (s, c)
  | step_Ite_true π s e c1 c2 :
    step (π, s, Ite e c1 c2) (Band π (beval s e), s, c1)
  | step_Ite_false π s e c1 c2 :
    step (π, s, Ite e c1 c2) (Band π (Bnot (beval s e)), s, c2)
  | step_Loop_true π s e c :
    step (π, s, Loop e c) (Band π (beval s e), s, Seq c (Loop e c))
  | step_Loop_false π s e c :
    step (π, s, Loop e c) (Band π (Bnot (beval s e)), s, Skip).

(** Reflexive transitive closure of [step] *)
Inductive steps : state -> state -> Prop :=
  | steps_refl s :
    steps s s
  | steps_step s1 s2 s3 :
    steps s1 s2 -> step s2 s3 -> steps s1 s3.

Lemma step_steps:
  forall s1 s2 s3, step s1 s2 -> steps s2 s3 -> steps s1 s3.
Proof.
  intros * H1 H2.
  induction H2 in s1, H1 |-*.
  - now repeat econstructor.
  - econstructor. apply IHsteps; eauto.
    apply H.
Qed.

Definition is_error '((_, _, prog) : state) :=
  Oracle.next_is_error prog.

Definition step' (s1 s2 : state) :=
  step s1 s2 /\ exists env, Concr.beval env (path s2) = true.

Inductive steps' : state -> state -> Prop :=
  | steps'_refl s :
    steps' s s
  | steps'_step s1 s2 s3 :
    steps' s1 s2 -> step' s2 s3 -> steps' s1 s3.

End Symb.

(** ** Connection between concrete and symbolic semantics *)

(** Compose a store and a symbolic store *)
Definition compose (env : Concr.store) (s : Symb.store) : Concr.store :=
  fun x => Concr.aeval env (s x).

Infix "∘" := (compose) (at level 70, no associativity).

Lemma id_comp :
  forall env, env ∘ Symb.id = env.
Proof.
  intros.
  now apply functional_extensionality.
Qed.

(** Evaluation of arithmetic expressions in a composed memory *)
Lemma aeval_comp:
  forall env senv e,
    Concr.aeval (env ∘ senv) e = Concr.aeval env (Symb.aeval senv e).
Proof.
  induction e; simpl; auto.
  - now rewrite IHe1, IHe2.
  - now rewrite IHe1, IHe2.
Qed.

(** Evaluation of boolean expressions in a composed memory *)
Lemma beval_comp:
  forall env senv e,
    Concr.beval (env ∘ senv) e = Concr.beval env (Symb.beval senv e).
Proof.
  induction e; simpl; auto.
  - now do 2 rewrite aeval_comp.
  - now do 2 rewrite aeval_comp.
  - now rewrite IHe.
  - now rewrite IHe1, IHe2.
Qed.

(** Memory updates in a composed memory *)
Lemma update_comp:
  forall env senv e x,
    env ∘ (Symb.update senv x (Symb.aeval senv e)) =
    Concr.update (env ∘ senv) x (Concr.aeval (env ∘ senv) e).
Proof.
  intros.
  apply functional_extensionality. intros y.
  unfold compose, Symb.update, Concr.update.
  destruct String.eqb; subst; auto.
  fold (compose env senv).
  now rewrite aeval_comp.
Qed.

(** Concretization of a symbolic state with a set of concrete inputs *)
Definition concretize_state env0 '((_, senv, p) : Symb.state) : Concr.state :=
  (env0 ∘ senv, p).
Notation "env0 • state" := (concretize_state env0 state) (at level 80).

(** What it means for a concrete state to "concretize" a symbolic
    state with respect to an initial memory
*)
Definition concretize_store (env0 : Concr.store) '((env, p) : Concr.state) '((π, senv, p') : Symb.state) : Prop :=
  Concr.beval env0 π = true /\ env = (env0 ∘ senv) /\ p = p'.
Notation "env0 ⊢ x ⊆ y" := (concretize_store env0 x y) (at level 80).

(** [Symb.step] is a complete complete abstraction of [Concr.step] *)
Lemma step_completeness:
  forall env0 s1 s1_sym s2,
    env0 ⊢ s1 ⊆ s1_sym ->
    Concr.step s1 s2 ->
    exists s2_sym,
      Symb.step s1_sym s2_sym /\ env0 ⊢ s2 ⊆ s2_sym.
Proof.
  intros * H1 H2.
  induction H2 as [ env x e v He | | | | | | ] in s1_sym, H1 |-*.
  - destruct s1_sym as [[path1 senv1] p1].
    destruct H1 as (Heval & -> & <-).
    eexists. split.
    apply Symb.step_Aff. reflexivity.
    repeat split; auto.
    now rewrite update_comp, He.
  - destruct s1_sym as [[path1 senv1] p1].
    destruct H1 as (Heval & -> & <-).
    specialize (IHstep (path1, senv1, c1)) as ([[path2 senv2] p2] & Hstep & Hconcr).
    split; auto.
    destruct Hconcr as (Heval2 & -> & <-).
    eexists. split.
    eapply Symb.step_Seq; eauto.
    repeat split; auto.
  - destruct s1_sym as [[path1 senv1] p1].
    destruct H1 as (Heval & -> & <-).
    eexists. split.
    eapply Symb.step_Seq_Skip.
    repeat split; auto.
  - destruct s1_sym as [[path1 senv1] p1].
    destruct H1 as (Heval & -> & <-).
    eexists. split.
    eapply Symb.step_Ite_true.
    repeat split; auto; simpl.
    now rewrite Heval, <- beval_comp, H.
  - destruct s1_sym as [[path1 senv1] p1].
    destruct H1 as (Heval & -> & <-).
    eexists. split.
    eapply Symb.step_Ite_false.
    repeat split; auto; simpl.
    now rewrite Heval, <- beval_comp, H.
  - destruct s1_sym as [[path1 senv1] p1].
    destruct H1 as (Heval & -> & <-).
    eexists. split.
    eapply Symb.step_Loop_true.
    repeat split; auto; simpl.
    now rewrite Heval, <- beval_comp, H.
  - destruct s1_sym as [[path1 senv1] p1].
    destruct H1 as (Heval & -> & <-).
    eexists. split.
    eapply Symb.step_Loop_false.
    repeat split; auto; simpl.
    now rewrite Heval, <- beval_comp, H.
Qed.

(** [Symb.steps] is a complete abstraction of [Concr.steps] *)
Lemma steps_completeness_1:
  forall env0 s1 s1_sym s2,
    env0 ⊢ s1 ⊆ s1_sym ->
    Concr.steps s1 s2 ->
    exists s2_sym,
      Symb.steps s1_sym s2_sym /\ env0 ⊢ s2 ⊆ s2_sym.
Proof.
  intros * H1 H2.
  induction H2 as [s1 | s1 s2 s3 Hsteps IH Hstep].
  - exists s1_sym. split; auto.
    apply Symb.steps_refl.
  - specialize (IH H1) as (s4_sym & Hsteps_sym & Hconcr).
    pose proof (step_completeness _ _ _ _ Hconcr Hstep) as (s2_sym & Hstep_sym & Hconcr').
    eexists. split.
    eapply Symb.steps_step.
    apply Hsteps_sym.
    eauto.
    eauto.
Qed.

(** [Symb.steps] can be used to detect runtime-errors *)
Corollary steps_completeness_2:
  forall p env,
    Concr.goes_wrong p env ->
    exists s,
      Symb.steps (Symb.init p) s /\
      Symb.is_error s = true /\
      Concr.beval env (Symb.path s) = true.
Proof.
  intros p env [[env2 p2] [Hsteps Hstuck]].
  assert (Hinit : env ⊢ (env, p) ⊆ Symb.init p) by easy.
  pose proof (Hsym := steps_completeness_1 env _ _ _ Hinit Hsteps). 
  destruct Hsym as ([[senv path] ?] & [H1 [H2 [H3 <-]]]).
  eexists _. repeat split; eauto.
  simpl.
  eapply Oracle.next_is_error_stuck; eauto.
Qed.

(** Path constraints can only be "growing" over one symbolic execution step *)
Lemma step_mono:
  forall env s1 s2,
    Symb.step s1 s2 ->
    Concr.beval env (Symb.path s2) = true ->
    Concr.beval env (Symb.path s1) = true.
Proof.
  intros * H1 H2.
  induction H1; auto; simpl in *.
  all: now apply Bool.andb_true_iff in H2 as [H2 _].
Qed.

(** Path constraints can only be "growing" over multiple symbolic execution steps *)
Lemma steps_mono:
  forall env s1 s2,
    Symb.steps s1 s2 ->
    Concr.beval env (Symb.path s2) = true ->
    Concr.beval env (Symb.path s1) = true.
Proof.
  intros env s1 s2 H1 H2.
  induction H1; auto; simpl in *.
  apply IHsteps.
  eapply step_mono; eauto.
Qed.

(** [Symb.step] is a sound abstraction of [Concr.step] *)
Lemma step_soundness:
  forall s1_sym s2_sym,
    Symb.step s1_sym s2_sym ->
    forall env0,
      Concr.beval env0 (Symb.path s2_sym) = true ->
      Concr.step (env0 • s1_sym) (env0 • s2_sym).
Proof.
  intros * H.
  induction H as [ | | [path senv] p | | | | ].
  - intros env0 Heval; subst. simpl in *.
    rewrite update_comp.
    now apply Concr.step_Aff.
  - intros env0 Heval; subst. simpl in *.
    apply Concr.step_Seq.
    now apply IHstep.
  - intros env0 Heval; subst. simpl in *.
    apply Concr.step_Seq_Skip.
  - intros env0 Heval; subst. simpl in *.
    apply Bool.andb_true_iff in Heval as [H1 H2].
    apply Concr.step_Ite_true.
    now rewrite beval_comp.
  - intros env0 Heval; subst. simpl in *.
    apply Bool.andb_true_iff in Heval as [H1 H2].
    apply Concr.step_Ite_false.
    apply Bool.negb_true_iff.
    now rewrite beval_comp.
  - intros env0 Heval; subst. simpl in *.
    apply Bool.andb_true_iff in Heval as [H1 H2].
    apply Concr.step_Loop_true.
    now rewrite beval_comp.
  - intros env0 Heval; subst. simpl in *.
    apply Bool.andb_true_iff in Heval as [H1 H2].
    apply Concr.step_Loop_false.
    apply Bool.negb_true_iff.
    now rewrite beval_comp.
Qed.

(** [Symb.steps] is a sound abstraction of [Concr.steps] *)
Lemma steps_soundness_1:
  forall s1_sym s2_sym,
    Symb.steps s1_sym s2_sym ->
    forall env,
      Concr.beval env (Symb.path s2_sym) = true ->
      Concr.steps (env • s1_sym) (env • s2_sym).
Proof.
  intros * H1. induction H1.
  - intros env Heval.
    apply Concr.steps_refl.
  - intros env Heval.
    eapply Concr.steps_step.
    apply IHsteps.
    eapply step_mono; eauto.
    now apply step_soundness.
Qed.

Corollary steps_soundness_2:
  forall p s,
    Symb.steps (Symb.init p) s ->
    Symb.is_error s = true ->
    forall env,
      Concr.beval env (Symb.path s) = true ->
      Concr.goes_wrong p env.
Proof.
  intros * Hsteps Herr env Henv.
  pose proof (H := steps_soundness_1 _ _ Hsteps _ Henv).
  eexists _. split.
  apply H. destruct s as [[path senv] p'].
  now apply Oracle.next_is_error_stuck.
Qed.

(** [Symb.step'] (adding pruning) is still a complete complete abstraction of [Concr.step] *)
Lemma step'_completeness:
  forall env0 s1 s1_sym s2,
    env0 ⊢ s1 ⊆ s1_sym ->
    Concr.step s1 s2 ->
    exists s2_sym,
      Symb.step' s1_sym s2_sym /\ env0 ⊢ s2 ⊆ s2_sym.
Proof.
  intros * H1 H2.
  pose proof (step_completeness _ _ _ _ H1 H2) as [s2_sym [H3 H4]].
  exists s2_sym. split; auto.
  split; auto.
  exists env0.
  destruct s2_sym as [[s2_path s2_mem] s2_cont]; simpl.
  destruct s2 as [env2 p2].
  apply H4.
Qed.

Lemma steps'_completeness:
  forall env0 s1 s1_sym s2,
    env0 ⊢ s1 ⊆ s1_sym ->
    Concr.steps s1 s2 ->
    exists s2_sym,
      Symb.steps' s1_sym s2_sym /\ env0 ⊢ s2 ⊆ s2_sym.
Proof.
  intros * H1 H2.
  induction H2.
  - exists s1_sym; repeat constructor; auto.
  - specialize (IHsteps H1) as [s2_sym [Hs2_sym_1 Hs2_sym_2]].
    pose proof (step'_completeness _ _ _ _ Hs2_sym_2 H) as [s3_sym [Hs3_sym_1 Hs3_sym_2]].
    eexists s3_sym. split; auto.
    eapply Symb.steps'_step; eauto.
Qed.

Lemma step'_mono:
  forall env s1 s2,
    Symb.step' s1 s2 ->
    Concr.beval env (Symb.path s2) = true ->
    Concr.beval env (Symb.path s1) = true.
Proof.
  intros * H1 H2.
  inversion H1.
  eapply step_mono; eauto.
Qed.

Lemma step'_soundness:
  forall s1_sym s2_sym,
    Symb.step' s1_sym s2_sym ->
    forall env0,
      Concr.beval env0 (Symb.path s2_sym) = true ->
      Concr.step (env0 • s1_sym) (env0 • s2_sym).
Proof.
  intros * H.
  inversion H as [H1 H2].
  now apply step_soundness.
Qed.

Lemma steps'_soundness:
  forall s1_sym s2_sym,
    Symb.steps' s1_sym s2_sym ->
    forall env,
      Concr.beval env (Symb.path s2_sym) = true ->
      Concr.steps (env • s1_sym) (env • s2_sym).
Proof.
  intros * H1. induction H1.
  - intros env Heval.
    apply Concr.steps_refl.
  - intros env Heval.
    eapply Concr.steps_step.
    apply IHsteps'.
    eapply step'_mono; eauto.
    now apply step'_soundness.
Qed.

(** ** Infinite streams *)

(** Finite or infinite streams *)
CoInductive stream A :=
  | snil
  | scons (x : A) (xs : stream A).
Arguments snil {_}.
Arguments scons {_}.

CoFixpoint map {A B} (f : A -> B) (s : stream A) : stream B :=
  match s with
  | snil => snil
  | scons x xs => scons (f x) (map f xs)
  end.

(** Get the i-th element of a stream *)
Fixpoint get {A} (s : stream A) (i : nat) : option A :=
  match i, s with
  | _, snil => None
  | 0, scons x _ => Some x
  | S i, scons _ s => get s i
  end.

(** Membership in a stream *)
Definition mem {A} (x : A) (s : stream A) : Prop :=
  exists i, get s i = Some x.

Theorem mem_map_1 {A B}:
  forall (s : stream A) (f : A -> B) x,
    mem x (map f s) -> exists y, x = f y /\ mem y s.
Proof.
  intros s f x [i Hi].
  induction i in s, Hi |-*; simpl in *.
  - destruct s as [|y s]; try easy.
    exists y. injection Hi as <-.
    split; auto. now exists 0.
  - destruct s as [|y s]; try easy.
    specialize (IHi _ Hi) as [z [-> [j Hj]]].
    exists z. split; auto.
    now exists (1 + j).
Qed.

Theorem mem_map_2 {A B}:
  forall (s : stream A) (f : A -> B) x,
    mem x s -> mem (f x) (map f s).
Proof.
  intros s f x [i Hi].
  induction i in s, Hi |-*; simpl in *.
  - destruct s as [|y s]; try easy.
    injection Hi as <-.
    now exists 0.
  - destruct s as [|y s]; try easy.
    specialize (IHi _ Hi) as [j Hj].
    now exists (1 + j).
Qed.

Inductive result A :=
  | Timeout
  | Found (x : A)
  | NotFound.
Arguments Timeout {_}.
Arguments Found {_}.
Arguments NotFound {_}.

(** ** Implementation of a symbolic bug finder for BUG *)

(** Proof-carrying witnesses that a command is either [Skip] or another command *)
Inductive skip_case (p : prog) : Type :=
  | is_skip : p = Skip -> skip_case p
  | is_not_skip : p <> Skip -> skip_case p.

(** Deciding if a command is [Skip] or another command.
    Using this decider instead of pattern matching
    reduces the number of cases from 6 to 2 in proofs.
*)
Definition skip_dec (p : prog) : skip_case p.
  destruct p.
  now apply is_skip.
  all: now apply is_not_skip.
Defined.

Module NaiveInterpreter.

(** Compute all symbolic sucessors of a state *)
Fixpoint expand path env prog : list Symb.state :=
  match prog with
  | Skip | Err => [ ]
  | Seq p1 p2 =>
    match skip_dec p1 with
    | is_skip _ _ => [ (path, env, p2) ]
    | is_not_skip _ _ =>
      List.map (fun '(path, senv, p) => (path, senv, Seq p p2)) (expand path env p1)
    end
  | Asg x e => [ (path, Symb.update env x (Symb.aeval env e), Skip) ]
  | Ite b p1 p2 => [
      (Band path (Symb.beval env b), env, p1);
      (Band path (Bnot (Symb.beval env b)), env, p2)
    ]
  | Loop b p => [
      (Band path (Symb.beval env b), env, Seq p (Loop b p));
      (Band path (Bnot (Symb.beval env b)), env, Skip)
    ]
  end.

(** [expand] computes exactly the symbolic successors *)
Theorem expand_sound_complete:
  forall path env prog s,
    In s (expand path env prog) <-> Symb.step (path, env, prog) s.
Proof.
  intros path env prog s. split.
  - intros Hin. induction prog in s, Hin |-*; simpl in *; try easy.
  + destruct Hin as [<- | [<- | []]]; constructor.
  + destruct skip_dec as [-> | _].
    * destruct Hin as [<- | []]; constructor.
    * apply in_map_iff in Hin as [[[path' env'] p'] [<- H2]].
      constructor. now apply IHprog1.
  + destruct Hin as [<- | []]; now constructor.
  + destruct Hin as [<- | [<- | []]]; now constructor.
  - intros Hstep. dependent induction Hstep; simpl in *; intuition.
    destruct skip_dec as [-> | _]; try easy.
    apply in_map_iff. eexists ((_, _), _). split; eauto.
Qed.


(** Compute a stream of symbolic states reachable from a list *)
CoFixpoint reachable (l : list Symb.state) : stream Symb.state :=
  match l with
  | [] => snil
  | (path, senv, p) as s::l => scons s (reachable (l ++ expand path senv p))
  end.

(** The [n]-th element of a list of initial states is reached after [n] steps *)
Lemma get_reachable:
  forall s l1 l2, get (reachable (l1 ++ s :: l2)) (List.length l1) = Some s.
Proof.
  intros [[path1 env1] prog1].
  induction l1 as [|[[path2 env2] prog2] l1 IH]; intros; simpl in *; auto.
  rewrite <- app_assoc. simpl.
  now rewrite IH.
Qed.

(** All states of the initial list are reached *)
Lemma mem_reachable_1:
  forall s l,
    In s l -> mem s (reachable l).
Proof.
  intros s l (l1 & l2 & ->)%In_split.
  exists (List.length l1).
  apply get_reachable.
Qed.

(** All successors of a reached state are also reached *)
Lemma mem_reachable_2:
  forall s1 s2 l,
    mem s1 (reachable l) -> Symb.step s1 s2 -> mem s2 (reachable l).
Proof.
  intros * [i Hi] Hsteps.
  induction i in l, Hi |-*; simpl in *.
  - destruct l as [| [[path env] prog] l]; try easy.
    injection Hi as <-.
    apply expand_sound_complete in Hsteps.
    apply In_split in Hsteps as (l1 & l2 & H).
    exists (S (List.length l) + List.length l1).
    simpl. rewrite H.
    rewrite app_assoc, <- app_length.
    apply get_reachable.
  - destruct l as [| [[path env] prog] l]; try easy.
    specialize (IHi _ Hi) as [j Hj].
    now exists (S j).
Qed.

(** [reachable] computes exactly all reachable states *)
Theorem reachable_sound_complete:
  forall l s2,
    mem s2 (reachable l) <-> exists s1, In s1 l /\ Symb.steps s1 s2.
Proof.
  intros. split.
  - intros [i Hi].
    induction i in s2, l, Hi |-*; simpl in *.
  + destruct l as [|[[path env] prog] l]; try easy.
    injection Hi as <-. eexists _. split.
    now left. constructor.
  + destruct l as [|[[path env] prog] l]; try easy.
    specialize (IHi _ _ Hi) as [s1 [[H1 | H1]%in_app_iff H2]].
  * exists s1. split; auto. now right.
  * eexists _. split. now left.
    eapply Symb.step_steps; eauto.
    now apply expand_sound_complete.
  - intros [s1 [Hin Hsteps]].
    induction Hsteps in Hin, l |-*.
  + now apply mem_reachable_1.
  + specialize (IHHsteps _ Hin).
    eapply mem_reachable_2; eauto.
Qed.

End NaiveInterpreter.

Inductive solver_result :=
  | SAT
  | UNSAT
  | TIMEOUT.

Module Type SOLVER.

Parameter check_sat : bexpr -> solver_result.
Axiom check_SAT :
  forall b, check_sat b = SAT -> exists sol, Concr.beval sol b = true.
Axiom check_UNSAT :
  forall b, check_sat b = UNSAT -> forall sol, Concr.beval sol b = false.
End SOLVER.

Module MakeInterpreter(Solver : SOLVER).

Definition expand '((path, env, prog) : Symb.state) :=
  List.filter (fun '(path, env, prog) =>
    match Solver.check_sat path with
    | UNSAT => false
    | _ => true
    end
  ) (NaiveInterpreter.expand path env prog).

Theorem expand_sound:
  forall s1 s2,
    In s2 (expand s1) -> Symb.step s1 s2.
Proof.
  intros [[path1 env1] p1] [[path2 env2] p2].
  now intros [Hin%NaiveInterpreter.expand_sound_complete Hsat]%filter_In.
Qed.

Theorem expand_complete:
  forall s1 s2,
    Symb.step' s1 s2 -> In s2 (expand s1).
Proof.
  intros [[path1 env1] p1] [[path2 env2] p2].
  intros [Hstep%NaiveInterpreter.expand_sound_complete [env Henv]].
  apply filter_In. split; auto.
  destruct Solver.check_sat eqn:Hsat; auto.
  eapply Solver.check_UNSAT in Hsat.
  now rewrite Hsat in Henv.
Qed.

(** Compute a stream of symbolic states reachable from a list *)
CoFixpoint reachable (l : list Symb.state) : stream Symb.state :=
  match l with
  | [] => snil
  | s::l => scons s (reachable (l ++ expand s))
  end.

(** The [n]-th element of a list of initial states is reached after [n] steps *)
Lemma get_reachable:
  forall s l1 l2, get (reachable (l1 ++ s :: l2)) (List.length l1) = Some s.
Proof.
  intros [[path1 env1] prog1].
  induction l1 as [|[[path2 env2] prog2] l1 IH]; intros; simpl in *; auto.
  rewrite <- app_assoc. simpl.
  now rewrite IH.
Qed.

(** All states of the initial list are reached *)
Lemma mem_reachable_1:
  forall s l,
    In s l -> mem s (reachable l).
Proof.
  intros s l (l1 & l2 & ->)%In_split.
  exists (List.length l1).
  apply get_reachable.
Qed.

(** All successors of a reached state are also reached *)
Lemma mem_reachable_2:
  forall s1 s2 l,
    mem s1 (reachable l) -> Symb.step' s1 s2 -> mem s2 (reachable l).
Proof.
  intros * [i Hi] Hsteps.
  induction i in l, Hi |-*; simpl in *.
  - destruct l as [| [[path env] prog] l]; try easy.
    injection Hi as <-.
    apply expand_complete in Hsteps.
    apply In_split in Hsteps as (l1 & l2 & H).
    exists (S (List.length l) + List.length l1).
    simpl. unfold expand in H. rewrite H.
    rewrite app_assoc, <- app_length.
    apply get_reachable.
  - destruct l as [| [[path env] prog] l]; try easy.
    specialize (IHi _ Hi) as [j Hj].
    now exists (S j).
Qed.

Theorem reachable_sound:
  forall l s2,
    mem s2 (reachable l) -> exists s1, In s1 l /\ Symb.steps s1 s2.
Proof.
  intros l s2 [i Hi].
  induction i in s2, l, Hi |-*; simpl in *.
  + destruct l as [|[[path env] prog] l]; try easy.
    injection Hi as <-. eexists _. split.
    now left. constructor.
  + destruct l as [|[[path env] prog] l]; try easy.
    specialize (IHi _ _ Hi) as [s1 [[H1 | H1]%in_app_iff H2]].
  * exists s1. split; auto. now right.
  * eexists _. split. now left.
    eapply Symb.step_steps; eauto.
    now apply expand_sound.
Qed.

Theorem reachable_complete:
  forall l s1 s2,
    In s1 l -> Symb.steps' s1 s2 -> mem s2 (reachable l).
Proof.
  intros l s1 s2 Hin Hsteps.
  induction Hsteps in Hin, l |-*.
  + now apply mem_reachable_1.
  + specialize (IHHsteps _ Hin).
    eapply mem_reachable_2; eauto.
Qed.

End MakeInterpreter.

Module Spec.

Definition is_bug (p : prog) (ass : bexpr) (bad : Concr.store) :=
  Concr.beval bad ass = true /\ Concr.goes_wrong p bad.

(** Any solution to [wit] is a bug triggering input that satisfies the assumptions [ass] *)
Definition has_potential_bug (p : prog) (ass : bexpr) (wit : bexpr) :=
  forall bad, Concr.beval bad wit = true -> is_bug p ass bad.

(** Under assumptions [ass], [p] has a bug when executed with [wit] *)
Definition has_sure_bug (p : prog) (ass : bexpr) (wit : bexpr) :=
  has_potential_bug p ass wit /\ exists bad, Concr.beval bad wit = true.

(** [p] is free of bugs under assumptions [ass] *)
Definition is_bug_free (p : prog) (ass : bexpr) :=
  forall env, Concr.beval env ass = true -> ~(Concr.goes_wrong p env).

End Spec.

Inductive bug :=
  | SureBug (path : bexpr)
  | UnsureBug (path : bexpr)
  | NoBug.

Module MakeNaiveBugFinder(Import Solver : SOLVER).

Definition is_error (s : Symb.state) :=
  if Symb.is_error s then
    match check_sat (Symb.path s) with
    | UNSAT => NoBug
    | SAT => SureBug (Symb.path s)
    | TIMEOUT => UnsureBug (Symb.path s)
    end
  else NoBug.

Definition find_bugs (p : prog) (ass : bexpr) :=
  map is_error (NaiveInterpreter.reachable [(ass, fun x => Var x, p)]).

Theorem find_bugs_precise_1:
  forall p ass wit,
    mem (SureBug wit) (find_bugs p ass) -> Spec.has_sure_bug p ass wit.
Proof.
  intros p ass wit [s [Hs1 Hs2]]%mem_map_1.
  apply NaiveInterpreter.reachable_sound_complete in Hs2 as (s1 & [[<-|[]] Hsteps]).
  split.
  - unfold is_error in Hs1.
    destruct Symb.is_error eqn:Herr; try easy.
    destruct check_sat eqn:Hsat; try easy.
    intros env Henv. injection Hs1 as ->.
    pose proof (Hass := steps_mono _ _ _ Hsteps Henv).
    split; auto.
    eexists _. split.
    apply (steps_soundness_1 _ _ Hsteps env Henv).
    destruct s as [[path senv] p']; simpl.
    intros Hcontr; try easy.
    eapply Oracle.next_is_error_stuck; eauto.
  - unfold is_error in Hs1.
    destruct Symb.is_error eqn:Herr; try easy.
    destruct check_sat eqn:Hsat; try easy.
    apply check_SAT in Hsat as [bad Hsat].
    pose proof (Hass := steps_mono _ _ _ Hsteps Hsat).
    injection Hs1 as ->. now exists bad.
Qed.

Theorem find_bugs_precise_2:
  forall p ass wit,
    mem (UnsureBug wit) (find_bugs p ass) -> Spec.has_potential_bug p ass wit.
Proof.
  intros p ass wit [s [Hs1 Hs2]]%mem_map_1.
  apply NaiveInterpreter.reachable_sound_complete in Hs2 as (s1 & [[<-|[]] Hsteps]).
  unfold is_error in Hs1.
  destruct Symb.is_error eqn:Herr; try easy.
  destruct check_sat eqn:Hsat; try easy.
  intros env Henv. injection Hs1 as ->.
  pose proof (Hass := steps_mono _ _ _ Hsteps Henv).
  split; auto.
  eexists _. split.
  apply (steps_soundness_1 _ _ Hsteps env Henv).
  destruct s as [[path senv] p']; simpl.
  intros Hcontr; try easy.
  eapply Oracle.next_is_error_stuck; eauto.
Qed.

Theorem find_bugs_exhaustive_1:
  forall p ass,
    (forall x, mem x (find_bugs p ass) -> x = NoBug) ->
    Spec.is_bug_free p ass.
Proof.
  intros p ass H.
  intros env Henv [s [Hs1 Hs2]].
  assert (Hconcr : env ⊢ (env, p) ⊆ (ass, fun x => Var x, p)) by easy.
  pose proof (steps_completeness_1 _ _ _ _ Hconcr Hs1) as [s3 [Hs3_1 Hs3_2]].
  assert (Hbad : mem (is_error s3) (find_bugs p ass)).
  apply mem_map_2, NaiveInterpreter.reachable_sound_complete.
  eexists _. split; eauto. now left.
  unfold is_error in Hbad.
  destruct s as [env' p'].
  destruct s3 as [[path' senv'] ?].
  destruct Hs3_2 as [H1 [-> <-]].
  apply Oracle.next_is_error_stuck in Hs2.
  simpl in *. rewrite Hs2 in Hbad.
  destruct check_sat eqn:Hsat.
  - now specialize (H _ Hbad).
  - eapply check_UNSAT in Hsat.
    now rewrite Hsat in H1.
  - now specialize (H _ Hbad).
Qed.

Theorem find_bugs_exhaustive_2:
  forall p ass bad,
    Spec.is_bug p ass bad ->
    exists wit,
      Concr.beval bad wit = true /\
        (mem (SureBug wit) (find_bugs p ass) \/
        mem (UnsureBug wit) (find_bugs p ass)).
Proof.
  intros p ass bad [Hbad [[env' p'] [H1 H2]]].
  assert (Hconcr : bad ⊢ (bad, p) ⊆ (ass, fun x => Var x, p)) by easy.
  pose proof (steps_completeness_1 _ _ _ _ Hconcr H1) as [[[path senv'] ?] [H3 H4]].
  destruct H4 as [Hpath [-> <-]].
  eapply Oracle.next_is_error_stuck in H2.
  pose proof NaiveInterpreter.reachable_sound_complete.
  assert (Hmem : mem (is_error (path, senv', p')) (find_bugs p ass)).
  apply mem_map_2, NaiveInterpreter.reachable_sound_complete.
  eexists _. split; eauto. now left.
  destruct (check_sat path) eqn:Hsat.
  - unfold is_error in Hmem. simpl in *.
    rewrite H2, Hsat in Hmem.
    eexists path. split; auto.
  - eapply check_UNSAT in Hsat.
    now rewrite Hsat in Hpath.
  - unfold is_error in Hmem. simpl in *.
    rewrite H2, Hsat in Hmem.
    eexists path. split; auto.
Qed.

End MakeNaiveBugFinder.

Module MakeBugFinder(Import Solver : SOLVER).

Module Interpreter := MakeInterpreter(Solver).

Definition is_error (s : Symb.state) :=
  if Symb.is_error s then
    match check_sat (Symb.path s) with
    | UNSAT => NoBug
    | SAT => SureBug (Symb.path s)
    | TIMEOUT => UnsureBug (Symb.path s)
    end
  else NoBug.

Definition find_bugs (p : prog) (ass : bexpr) :=
  map is_error (Interpreter.reachable [(ass, fun x => Var x, p)]).

Theorem find_bugs_precise_1:
  forall p ass wit,
    mem (SureBug wit) (find_bugs p ass) -> Spec.has_sure_bug p ass wit.
Proof.
  intros p ass wit [s [Hs1 Hs2]]%mem_map_1.
  apply Interpreter.reachable_sound in Hs2 as (s1 & [[<-|[]] Hsteps]).
  split.
  - unfold is_error in Hs1.
    destruct Symb.is_error eqn:Herr; try easy.
    destruct check_sat eqn:Hsat; try easy.
    intros env Henv. injection Hs1 as ->.
    pose proof (Hass := steps_mono _ _ _ Hsteps Henv).
    split; auto.
    eexists _. split.
    apply (steps_soundness_1 _ _ Hsteps env Henv).
    destruct s as [[path senv] p']; simpl.
    intros Hcontr; try easy.
    eapply Oracle.next_is_error_stuck; eauto.
  - unfold is_error in Hs1.
    destruct Symb.is_error eqn:Herr; try easy.
    destruct check_sat eqn:Hsat; try easy.
    apply check_SAT in Hsat as [bad Hsat].
    pose proof (Hass := steps_mono _ _ _ Hsteps Hsat).
    injection Hs1 as ->. now exists bad.
Qed.

Theorem find_bugs_precise_2:
  forall p ass wit,
    mem (UnsureBug wit) (find_bugs p ass) -> Spec.has_potential_bug p ass wit.
Proof.
  intros p ass wit [s [Hs1 Hs2]]%mem_map_1.
  apply Interpreter.reachable_sound in Hs2 as (s1 & [[<-|[]] Hsteps]).
  unfold is_error in Hs1.
  destruct Symb.is_error eqn:Herr; try easy.
  destruct check_sat eqn:Hsat; try easy.
  intros env Henv. injection Hs1 as ->.
  pose proof (Hass := steps_mono _ _ _ Hsteps Henv).
  split; auto.
  eexists _. split.
  apply (steps_soundness_1 _ _ Hsteps env Henv).
  destruct s as [[path senv] p']; simpl.
  intros Hcontr; try easy.
  eapply Oracle.next_is_error_stuck; eauto.
Qed.

Theorem find_bugs_exhaustive_1:
  forall p ass,
    (forall x, mem x (find_bugs p ass) -> x = NoBug) ->
    Spec.is_bug_free p ass.
Proof.
  intros p ass H.
  intros env Henv [s [Hs1 Hs2]].
  assert (Hconcr : env ⊢ (env, p) ⊆ (ass, fun x => Var x, p)) by easy.
  pose proof (steps'_completeness _ _ _ _ Hconcr Hs1) as [s3 [Hs3_1 Hs3_2]].
  assert (Hbad : mem (is_error s3) (find_bugs p ass)).
  eapply mem_map_2, Interpreter.reachable_complete.
  now left. auto.
  destruct s as [env' p'].
  destruct s3 as [[path' senv'] ?].
  destruct Hs3_2 as [H1 [-> <-]].
  apply Oracle.next_is_error_stuck in Hs2.
  simpl in *. unfold is_error in Hbad.
  simpl in *. rewrite Hs2 in Hbad.
  destruct check_sat eqn:Hsat.
  - now specialize (H _ Hbad).
  - eapply check_UNSAT in Hsat.
    now rewrite Hsat in H1.
  - now specialize (H _ Hbad).
Qed.

Theorem find_bugs_exhaustive_2:
  forall p ass bad,
    Spec.is_bug p ass bad ->
    exists wit,
      Concr.beval bad wit = true /\
        (mem (SureBug wit) (find_bugs p ass) \/
        mem (UnsureBug wit) (find_bugs p ass)).
Proof.
  intros p ass bad [Hbad [[env' p'] [H1 H2]]].
  assert (Hconcr : bad ⊢ (bad, p) ⊆ (ass, fun x => Var x, p)) by easy.
  pose proof (steps'_completeness _ _ _ _ Hconcr H1) as [[[path senv'] ?] [H3 H4]].
  destruct H4 as [Hpath [-> <-]].
  eapply Oracle.next_is_error_stuck in H2.
  pose proof NaiveInterpreter.reachable_sound_complete.
  assert (Hmem : mem (is_error (path, senv', p')) (find_bugs p ass)).
  eapply mem_map_2, Interpreter.reachable_complete.
  now left. auto.
  destruct (check_sat path) eqn:Hsat.
  - unfold is_error in Hmem. simpl in *.
    rewrite H2, Hsat in Hmem.
    eexists path. split; auto.
  - eapply check_UNSAT in Hsat.
    now rewrite Hsat in Hpath.
  - unfold is_error in Hmem. simpl in *.
    rewrite H2, Hsat in Hmem.
    eexists path. split; auto.
Qed.

End MakeBugFinder.

From Coq Require Import Extraction.
(* Basic datatypes (pairs, lists, booleans) are extracted to OCaml's ones *)
From Coq Require Import ExtrOcamlBasic.
(* Strings are extracted to OCaml's lists of chars *)
From Coq Require Import ExtrOcamlString.
(* Integers are extracted to OCaml's Int *)
From Coq Require Import ExtrOcamlZInt.
From Coq Require Import ExtrOcamlNatInt.

Extraction "core.ml" MakeNaiveBugFinder MakeBugFinder.