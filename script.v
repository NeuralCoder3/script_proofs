
Notation "⊥" := False.
Notation "⊤" := True.
Notation "¬" := not.



(* (φ -> ψ) -> (φ -> ψ) *)
(* use intros *)
(* Ltac ImplIntro := intro. *)
Tactic Notation "ImplIntro" :=
    let h := fresh "H" in
    intro h.
Tactic Notation "ImplIntro" ident(x) :=
    intro x.

(* φ /\ ψ -> (φ -> ψ -> P) -> P *)
(* use destruct *)
Definition and_elim {A B P} H :=
  fun R => @and_rect A B P R H.
Ltac AndElim H :=
    apply (and_elim H); do 2 intro.
    (* let name := name of H in
    match type of H with
    | _ /\ _ => pose proof H;destruct H
    | _ => fail "only conjunctions can be eliminated using this rule"
    end. *)

(* φ -> ψ -> φ /\ ψ *)
(* use split *)
Ltac AndIntro := apply conj.
(* φ -> φ *)
(* use assumption *)
Ltac Assumption := assumption.

(* ⊤ *)
(* use easy *)
Ltac TruthIntro := exact I.

(* ⊥ -> P *)
(* use destruct *)
Ltac FalsityElim H :=
    exfalso;exact H.

(* (φ -> χ) -> (ψ -> χ) -> (φ \/ ψ -> χ) *)
(* use destruct *)
Definition or_elim {A B P} H :=
  fun R1 R2 => @or_ind A B P R1 R2 H.
Ltac OrElim H :=
    apply (or_elim H);intro.

(* φ -> φ \/ ψ *)
Ltac OrIntro1 := left.
(* ψ -> φ \/ ψ *)
Ltac OrIntro2 := right.

(* (φ -> ψ) -> φ -> ψ *)
Ltac ImplApply H :=
    apply H.

    (* TODO: test *)
Ltac ImplSpecialize H :=
    let fn := fresh in
    specialize H as fn.

Ltac NegElim H :=
    let fn := fresh in
    pose proof (fn := H); 
    unfold not in fn.

Ltac NegIntro :=
    ImplIntro.

Ltac Assert H := assert H.

Require Import Classical.

Ltac EitherOf P :=
    destruct (classic P).


Section S3_2_2.
  Variables (P Q:Prop).

  Goal P /\ Q -> Q /\ P.
  Proof.
    ImplIntro.
    AndElim H.
    AndIntro.
    - Assumption.
    - Assumption.
  Qed.

End S3_2_2.

Section S3_2_3.
  Variables (P Q R:Prop).

    Goal P \/ Q -> Q \/ P.
    Proof.
      ImplIntro H1.
      OrElim H1.
      - OrIntro2.
        Assumption.
      - OrIntro1.
        Assumption.
    Qed.

    Goal (P -> Q -> R) -> (P /\ Q -> R).
    Proof.
      ImplIntro H1.
      ImplIntro H2.
      AndElim H2.
      ImplSpecialize (H1 H).
      ImplApply H3.
      Assumption.
    Restart.
      (* coq notation *)
      intros H1 H2.
      destruct H2 as [H3 H4].
      specialize (H1 H3) as H5.
      apply H5.
      assumption.
    Restart.
      (* shorter *)
      intros H [HP HQ].
      apply (H HP HQ).
    Qed.

    Goal (P \/ Q -> R) -> (P -> R) /\ (Q -> R).
    Proof.
      ImplIntro.
      AndIntro.
      - ImplIntro.
        ImplApply H.
        OrIntro1.
        Assumption.
      - ImplIntro.
        ImplApply H.
        OrIntro2.
        Assumption.
    Qed.

    Goal P -> P /\ True.
    Proof.
      ImplIntro.
      AndIntro.
      - Assumption.
      - TruthIntro.
    Qed.

    Goal P \/ False -> P.
    Proof.
      ImplIntro.
      OrElim H.
      - Assumption.
      - FalsityElim H0.
    Qed.

    Goal (P -> Q \/ R) -> (P -> Q) \/ (P -> R).
    Proof.
      ImplIntro.
      EitherOf (P -> Q).
      - OrIntro1.
        Assumption.
      - OrIntro2.
        ImplIntro.
        ImplSpecialize (H H1).
        OrElim H2.
        + NegElim H0.
          Assert False.
          * ImplApply H4.
            ImplIntro.
            Assumption.
          * FalsityElim H5.
        + Assumption.
    Qed.

End S3_2_3.

Ltac Contradiction := apply NNPP;ImplIntro.

Section S3_2_4.

  Lemma Contradiction φ
    (Asm: ~ φ -> ⊥):
    φ.
  Proof.
    EitherOf φ.
    - Assumption.
    - Assert ⊥.
      + ImplApply (Asm H).
      + FalsityElim H0.
  Qed.

  Variables (P:Prop).

  Goal P \/ ¬ P.
  Proof.
    Contradiction.
    NegElim H.
    ImplApply H0.
    OrIntro2.
    NegIntro.
    ImplApply H0.
    OrIntro1.
    Assumption.
  Qed.
End S3_2_4.

Ltac NegElimApply H :=
  exfalso;apply H.
Ltac ExFalso := exfalso.

Ltac EquivChain Q :=
  transitivity Q.

Ltac ForallIntro n :=
  intro n.

Ltac ForallElim H v :=
  let fn := fresh in
  specialize (H v) as fn.

Ltac ExistsIntro t :=
  exists t.
Ltac ExistsElim H v :=
  destruct H as [v ?].

Section S3_3.

  Variable (X:Type).

  Example QuantHandling
    (P Q : X*X -> Prop):
    (forall x y, P (x,y) -> Q (y,x)) /\ 
    (forall x, P(x,x)) -> 
    forall y, Q (y,y).
  Proof.
    ImplIntro H1.
    AndElim H1.
    ForallIntro z.
    ForallElim H z.
    ForallElim H2 z.
    ImplApply H3.
    ForallElim H0 z.
    Assumption.
  Qed.

  Lemma L10 (φ:X*X -> Prop):
    (forall x, forall y, φ(x,y)) <->
    (forall x, forall y, φ(y,x)).
  Proof.
    AndIntro.
    - ImplIntro.
      ForallIntro x.
      ForallIntro y.
      ForallElim H y.
      ForallElim H0 x.
      Assumption.
    - ImplIntro.
      ForallIntro x.
      ForallIntro y.
      ForallElim H y.
      ForallElim H0 x.
      Assumption.
  Qed.



End S3_3.