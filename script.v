
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

Require Import Classical Lia.

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
  let fn := fresh in
  pose proof (fn := H);
  destruct fn as [v ?].

Ltac EqualsIntro := reflexivity.

Ltac EqualsElim H := rewrite H.
Tactic Notation "EqualsElim←" constr(H) := rewrite <- H.

(* not Axiom due to naming restriction *)
Ltac axiom H := pose proof H.
Ltac lemma H := pose proof H.

Ltac Defn H := unfold H.

Section S3_3.

  Variable (X:Type).
  Implicit Type (x y:X).

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

  Goal forall x y, x=y -> y=x.
  Proof.
    ForallIntro x.
    ForallIntro y.
    ImplIntro.
    EqualsElim H.
    EqualsIntro.
  Qed.

  (* Lemma 12 *)
  Lemma EqTrans:
    forall x y z, x=y -> y=z -> x=z.
  Proof.
    ForallIntro x.
    ForallIntro y.
    ForallIntro z.
    ImplIntro.
    ImplIntro.
    EqualsElim H.
    EqualsElim← H0.
    EqualsIntro.
  Qed.

  Definition leq n m := exists k, m = n+k.
  Notation "n ≤ m" := (leq n m) (at level 67).

  (* Lemma 13 *)
  Lemma LeqRefl: 
    forall n, n ≤ n.
  Proof.
    ForallIntro x.
    ExistsIntro 0.
    axiom plus_n_O.
    ForallElim H x.
    EqualsElim← H0.
    EqualsIntro.
  Restart.
    ForallIntro x.
    Defn leq.
    ExistsIntro 0.
    axiom plus_n_O.
    ForallElim H x.
    EqualsElim← H0.
    EqualsIntro.
  Qed.

  Definition divide (x:nat) n := exists k, x*k = n.
  Notation "x | n" := (divide x n) (at level 67).
  Definition even n := 2 | n.

  Lemma even_add:
    forall (x y:nat), 
      even x -> even y -> even (x+y).
  Proof.
    ForallIntro x.
    ForallIntro y.
    ImplIntro.
    ImplIntro.
    Defn even.
    Defn divide.
    ExistsElim H k1.
    ExistsElim H0 k2.
    ExistsIntro (k1+k2).
    axiom (PeanoNat.Nat.mul_add_distr_l).
    ForallElim H3 2.
    ForallElim H4 k1.
    ForallElim H5 k2.
    EqualsElim H6.
    EqualsElim← H1.
    EqualsElim← H2.
    EqualsIntro.
  Restart.
    (* shortened version *)
    intros x y [k1 H1] [k2 H2].
    unfold even, divide.
    exists (k1+k2).
    rewrite PeanoNat.Nat.mul_add_distr_l.
    rewrite H1,H2.
    reflexivity.
  Restart.
    (* even shorter *)
    intros.
    destruct H as [kx ?],H0 as [ky ?].
    exists (kx+ky).
    lia.
  Qed.

  Example ComplexApply
    (P:X*X -> Prop):
  (forall a b c, P (a,b) -> P(c,b) -> P(a,c)) -> forall a b, P(a,b) -> P(a,a).
  Proof.
    intros.
    apply (H a b a).
    - assumption.
    - assumption.
  Qed.

End S3_3.

Section S4.
  Variable (X:Type).
  Definition set X := X -> Prop.
  Notation "{ x1 , x2 , .. , xn }" := (fun x => or (x = x1) (or (x=x2) (.. (or (x = xn) True) ..))).
  (* only local or "only parsing" *)
  Local Notation " x ∈ A " := (A x) (only parsing, at level 67).
  Local Notation " x ∉ A " := (~(x∈A)) (only parsing, at level 67).
  (* Notation "{ x | P x }" := (P). *)
  (* {x | False} = (fun x => False) *)
  Definition emptyset := (fun (x:X) => False).
  Local Notation "∅" := emptyset.

  Definition union (A:set X) (B:set X) := (fun x => x ∈ A \/ x ∈ B).
  Local Notation "A ∪ B" := (union A B) (at level 67).
  Definition intersection (A:set X) (B:set X) := (fun x => x ∈ A /\ x ∈ B).
  Local Notation "A ∩ B" := (intersection A B) (at level 67).
  Definition difference (A:set X) (B:set X) := (fun x => x ∈ A /\ x ∉ B).
  Local Notation "A \ B" := (difference A B) (at level 67).
  Definition complement (A:set X) := (fun x => x ∉ A).
  Local Notation "! A" := (complement A) (at level 75).
  Definition subset (A:set X) (B:set X) := (forall x, x ∈ A -> x ∈ B).
  Local Notation "A ⊆ B" := (subset A B) (at level 67).
  Definition setequality (A:set X) (B:set X) := (forall x, x ∈ A <-> x ∈ B).
  Local Notation "A ≡ B" := (setequality A B) (at level 70).

  Theorem SetEqualitySubset A B:
    A ≡ B <-> A ⊆ B /\ B ⊆ A.
  Proof.
    (* Proof from the lecture notes *)
    split.
    - intros.
      unfold subset, setequality in *.
      now setoid_rewrite H.
    - now intros [H1 H2] x;split;[intros H%H1 | intros H%H2].
  Restart.
    (* single steps *)
    split.
    - intros.
      unfold setequality in H.
      split.
      + intros x HA.
        apply H.
        assumption.
      + intros x HB.
        apply H.
        assumption.
    - intros [H1 H2] x. 
      split.
      + intros HA.
        specialize (H1 x).
        apply H1 in HA.
        assumption.
      + intros HB.
        specialize (H2 x).
        apply H2 in HB.
        assumption.
    Restart.
      (* short with automation *)
      split.
      - intros. split;intros x Hx;specialize (H x);now apply H.
      - intros [] ?. split; eauto.
    Restart.
      firstorder.
    Qed.

  Theorem DifferenceComplement A B:
    A \ B ≡ (!B) ∩  A.
  Proof.
    split.
    - intros H.
      destruct H.
      split.
      + apply H0.
      + assumption.
    - intros H.
      destruct H.
      split.
      + assumption.
      + apply H.
  Qed.

  Definition cart_product {X Y} (A:set X) (B:set Y) := 
    (fun '(a,b) => a ∈ A /\ b ∈ B).

  Lemma disjoint_difference A B:
    (A \ B) ∩ (A ∩ B) ≡ ∅.
  Proof.
    (* proof from the script but without contraposition *)
    split.
    - intros [[] []].
      contradict H0.
      assumption.
    - intros H. contradict H.
  Qed.
    
  Lemma commutative_intersection A B:
    A ∩ B ≡ B ∩ A.
  Proof.
    firstorder.
  Qed.

  Theorem disjoint_decomposition (A:set X) (B:set X) :
    A ∪ B ≡ (A \ B) ∪ (B \ A) ∪ (A ∩ B) /\
    (
      (A\B) ∩ (B\A) ≡ ∅ /\
      (A\B) ∩ (A ∩ B) ≡ ∅ /\
      (B\A) ∩ (A ∩ B) ≡ ∅
    )
    .
    Proof.
      split.
      - split.
        (* ⊆ *)
        + intros H.
          destruct H.
          * destruct (classic (x ∈ B)).
            -- right. split;assumption.
            -- left. left. split;assumption.
          * destruct (classic (x ∈ A)).
            -- right. split;assumption.
            -- left. right. split;assumption.
        (* ⊇ *)
        + intros H.
          destruct H as [[H | H] | H].
          all: destruct H.
          * left. assumption.
          * right. assumption.
          * left. assumption.
      (* disjooint *)
      - split;[|split].
        + split. 2: easy. (* 2 is easy because it is contradictory *)
          intros [[][]].
          contradict H0.
          assumption.
        + apply disjoint_difference.
        (* TODO: use lemma *)
        + split. 2: easy. 
          intros [[][]].
          contradict H0.
          assumption.
    Qed.

    (* TODO: cardinality *)

    Definition powerset (A:set X) := (fun x => x ⊆ A).

    Theorem T12 A:
      ∅ ∈ powerset A /\ A ∈ powerset A.
    Proof.
      split;intros x Hx.
      - contradict Hx.
      - assumption.
    Qed.


    Section Relations.
      (* TODO: relations *)
      Variable (A B : Type).
      Implicit Type (a:A) (b:B).

      Definition left_total R :=
          forall a, exists b, R (a,b).

      Definition surjective R :=
          forall b, exists a, R (a,b).

      Definition injective R :=
          forall a1 a2, forall b,
          R (a1,b) -> R (a2,b) -> a1 = a2.

      Definition functional R :=
          forall b1 b2, forall a,
          R (a,b1) -> R (a,b2) -> b1 = b2.

      Definition bijective R := 
        surjective R /\ injective R.

      Definition total_function R :=
        left_total R /\ functional R.

      Definition bijection R :=
        total_function R /\ bijective R.

      (* Z -> N
          (BinNums)
          2x
          -2x-1
      *)

    End Relations.


End S4.