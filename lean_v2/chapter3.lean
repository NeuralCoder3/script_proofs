open Classical -- for exclude middle

theorem intro_example (X: Type) (P Q: X×X→Prop):
  (∀ x y, P (x, y) -> Q (x, y)) ->
  (∀ x, P (x, x)) ->
  ∀ y, Q (y, y) := by
  intro h1 h2 y
  apply h1
  apply h2

theorem l3_1 (P Q: Prop):
  P ∧ Q -> Q ∧ P := by
  intro H -- ImplIntro
  obtain ⟨HP, HQ⟩ := H -- AndElim
  constructor -- AndIntro
  . exact HQ -- Assumption
  . exact HP -- Assumption


theorem f3_3 (P Q: Prop):
  P ∧ Q -> Q ∧ P := by
  intro H1 -- ImplIntro
  constructor -- AndIntro
  . obtain ⟨H2, H3⟩ := H1 -- AndElim
    exact H3 -- Assumption
  . obtain ⟨H2, H3⟩ := H1 -- AndElim
    exact H2 -- Assumption

theorem f3_4 (P Q: Prop):
  P ∨ Q -> Q ∨ P := by
  intro H -- ImplIntro
  cases H with -- OrElim H1
  | inl HP =>
    right -- OrIntro2
    assumption -- Assumption H2
  | inr HQ =>
    left -- OrIntro1
    assumption -- Assumption H3

theorem f3_5 (P Q R: Prop):
  (P -> Q -> R) -> (P ∧ Q -> R) := by
  intro H1 -- ImplIntro
  intro H2 -- ImplIntro
  obtain ⟨H3, H4⟩ := H2 -- AndElim H2
  specialize H1 H3 -- ImplSpecialize H1 H3
  apply H1 -- ImplApply H5
  assumption -- Assumption H4

theorem f3_6 (P Q R: Prop):
  (P ∨ Q -> R) -> (P -> R) ∧ (Q -> R) := by
  intro H1 -- ImplIntro
  constructor -- AndIntro
  . intro H2 -- ImplIntro
    apply H1 -- ImplApply
    left -- OrIntro1
    assumption -- Assumption H2
  . intro H2 -- ImplIntro
    apply H1 -- ImplApply
    right -- OrIntro2
    assumption -- Assumption H2

theorem f3_7 (P: Prop):
  P -> P ∧ True := by
  intro H1 -- ImplIntro
  constructor -- AndIntro
  . exact H1 -- Assumption
  . trivial -- TruthIntro

theorem f3_8 (P: Prop):
  P ∨ False -> P := by
  intro H1 -- ImplIntro
  cases H1 with -- OrElim H1
  | inl H2 =>
    assumption -- Assumption H2
  | inr H3 =>
    contradiction -- FalseElim H3

-- alternative in new syntax
theorem f3_8' (P: Prop):
  P ∨ False -> P := by
  intro H1 -- ImplIntro
  obtain H2 | H3 := H1 -- OrElim H1
  . assumption -- Assumption H2
  . contradiction -- FalseElim H3

theorem f3_9 (P Q: Prop):
  (P -> Q) -> (¬Q -> ¬P) := by
  intro H1 -- ImplIntro
  intro H2 -- ImplIntro
  have H3 := H2 -- copy
  unfold Not at H3 -- NegElim H2 (not necessary in Lean)
  intro H4 -- NegIntro
  apply H3 -- ImplApply H3
  apply H1 -- ImplApply H1
  assumption -- Assumption H4

theorem f3_10 (P Q R: Prop):
  (P -> Q ∨ R) -> (P -> Q) ∨ (P -> R) := by
  intro H1 -- ImplIntro
  obtain H2 | H3 := em (P -> Q) -- ExludeMiddle (P -> Q)
  . left -- OrIntro1
    assumption -- Assumption H2
  . right -- OrIntro2
    intro H4 -- ImplIntro
    have H5 := H1
    specialize H5 H4 -- ImplSpecialize H1 H4
    obtain H6 | H10 := H5 -- OrElim H5
    . have H7 := H3 -- copy
      unfold Not at H7 -- NegElim H3
      have H9 : False := by {
        apply H7 -- ImplApply H7
        intro H8 -- ImplIntro
        assumption -- Assumption H6
      }
      contradiction -- FalseElim H9
    . assumption -- Assumption H10

-- a bit shorter
theorem f3_10':
  (P -> Q ∨ R) -> (P -> Q) ∨ (P -> R) := by
  intro H
  by_cases H3 : P -> Q
  . left;trivial
  . right
    intro HP
    obtain HQ | HR := H HP
    . exfalso;apply H3;intro;assumption
    . assumption

theorem contradiction (H: ¬ϕ -> False):
  ϕ := by
  obtain H1 | HC := em ϕ -- ExludeMiddle ϕ
  . assumption -- assumption H1
  . have H2: False := H HC -- The remaining proof of the contradiction rule (here an assumption)
    contradiction -- FalseElim H2

theorem f3_13: P ∨ ¬P := by
  apply contradiction;intro H1 -- Contradiction
  -- NegElim H1
  apply H1 -- ImplApply H2
  right -- OrIntro2
  intro H3 -- NegIntro
  apply H1 -- ImplApply H2
  left -- OrIntro1
  assumption -- Assumption H3



-- Chapter 3.2
theorem f3_16 (P Q: X×X→Prop):
  (forall x y, P (x,y) -> Q (y,x)) ∧ (forall x, P (x,x)) ->
  forall y, Q (y,y) := by
  intro H1 -- ImplIntro
  obtain ⟨H2, H3⟩ := H1 -- AndElim H1
  intro z -- ForallIntro z
  specialize H2 z z -- ImplSpecialize H2 z; ImplSpecialize H4 z
  apply H2 -- ImplApply H5
  specialize H3 z -- ImplSpecialize H3 z
  assumption -- Assumption H6

theorem f3_17 (ϕ : X×X -> Prop):
  (forall x y: X, ϕ (x,y)) <-> (forall y x, ϕ (x,y)) := by
  constructor -- AndIntro
  . intro H1 -- ImplIntro
    intro y -- ForallIntro y
    intro x -- ForallIntro x
    specialize H1 x -- ForallElim H1 y
    specialize H1 y -- ForallElim H2 y
    assumption -- Assumption H3
  . intro H1 -- ImplIntro
    intro x -- ForallIntro x
    intro y -- ForallIntro y
    specialize H1 y -- ForallElim H1 y
    specialize H1 x -- ForallElim H2 x
    assumption -- Assumption H3

theorem l3_20_symmetry:
  forall x y : X, x=y -> y=x := by
  intro x y -- ForallIntro x, ForallIntro y
  intro H1 -- ImplIntro
  rewrite [H1] -- EqualsElim H1
  rfl -- EqualsIntro

theorem l3_22_transitivity:
  forall x y z : X, x=y -> y=z -> x=z := by
  intro x y z -- ForallIntro x, ForallIntro y, ForallIntro z
  intro H1 -- ImplIntro
  intro H2 -- ImplIntro
  rewrite [H1, <- H2] -- EqualsElim H1, EqualsElim <- H2
  rfl -- EqualsIntro

theorem l3_22_transitivity_c3_24:
  forall x y z : X, x=y -> y=z -> x=z := by
  intro x y z -- ForallIntro x, ForallIntro y, ForallIntro z
  intro H1 -- ImplIntro
  intro H2 -- ImplIntro
  rewrite [<- H2] -- EqualsElim <- H2
  assumption -- Assumption H1

theorem f3_25 (P: X -> Prop):
  forall x y, x=y -> P x -> P y := by
  intro x y -- ForallIntro x, ForallIntro y
  intro H1 -- ImplIntro
  intro H2 -- ImplIntro
  rewrite [H1] at H2 -- EqualsRewrite H2 with H1
  assumption -- Assumption H3

theorem l3_32_refl:
  forall x:Nat, x ≤ x := by
  intro x -- ForallIntro x
  apply (@Nat.le.intro x x 0) -- we need to apply a lemma instead of ExistsIntro0
  -- the other direction is Nat.le.dest
  have A1 := Nat.add_zero -- Axiom
  specialize A1 x -- ImplSpecialize A1 x
  rewrite [A1] -- EqualsElim H2
  rfl -- EqualsIntro

theorem c3_35: 0 <= 0 := by
  have L1 := l3_32_refl -- Lemma 3.32
  specialize L1 0 -- ImplSpecialize L1 0
  assumption -- Assumption H1

def even (x: Nat) := exists k, x = 2*k

theorem f3_38:
  forall x y, even x -> even y -> even (x+y) := by
  intro x -- ForallIntro x
  intro y -- ForallIntro y
  intro H1 -- ImplIntro
  intro H2 -- ImplIntro
  unfold even at H1 H2 -- Unfold even
  obtain ⟨k1, H3⟩ := H1 -- ExistsElim H1 k1
  obtain ⟨k2, H4⟩ := H2 -- ExistsElim H2 k2
  exists k1+k2 -- ExistsIntro k1+k2
  have A1 := Nat.mul_add -- Axiom distributivity
  specialize A1 2 -- ForallElim A1 2
  specialize A1 k1 -- ImplSpecialize H5 k1
  specialize A1 k2 -- ImplSpecialize H6 k2
  rewrite [A1] -- EqualsElim H3
  rewrite [<- H3] -- EqualsElim <- H3
  rewrite [<- H4] -- EqualsElim <- H4
  rfl -- EqualsIntro


theorem f3_38':
  forall x y, even x -> even y -> even (x+y) := by
  intro x y Hx Hy
  obtain ⟨kx, Hx⟩ := Hx
  obtain ⟨ky, Hy⟩ := Hy
  exists kx+ky
  rw [Nat.mul_add, <- Hx, <- Hy]

theorem f3_41 (P: X×X→Prop):
  (forall a b c, P (a,b) -> P (c,b) -> P (a,c)) ->
  forall a b, P (a,b) -> P (a,a) := by
  intro H1 a b H2
  apply (H1 a b a H2 H2)

theorem l3_44 (P: X×X→Prop):
  (forall x y, P (x,y) -> x=y) ->
  forall x y z, P (x,y) -> P (y,z) -> P (x,z) := by
  intro H1 x y z H2 H3
  have H4 := H1 x y H2
  rewrite [H4]
  assumption
