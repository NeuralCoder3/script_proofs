import set_theory.cardinal
import data.nat.basic

-- with lean + vscode lean plugin installed:
--   open in the lean_script folder
-- alternative: https://leanprover.github.io/live/latest/

-- Lean uses slightly different names for the proof rules.
-- 
-- For instance, 
--   ImplIntro is called "intro" in Lean.
--   AndElim is "apply (and.elim H), intros," or just "cases H".
--   AndIntro is "apply and.intro" or just "split"
-- 
-- we will use the Lean names for the proof rules.

section proplogic

variables (P Q R : Prop)

example: (P /\ Q -> Q /\ P) :=
begin
    intro H,
    cases H,
    split,
    repeat { assumption },
end

-- more in line with script
example: (P /\ Q -> Q /\ P) :=
begin
  intro H,
  apply and.elim H, intros HP HQ,
  apply and.intro, 
  {
    assumption
  },
  {
    assumption
  },
end

example: P \/ Q -> Q \/ P :=
begin
  intro H,
  cases H,
  {
    right,
    assumption
  },
  {
    left,
    assumption
  },
end

example: (P -> Q -> R) -> (P /\ Q -> R) :=
begin
  intros H1 H2,
  cases H2,
  specialize (H1 H2_left),
  apply H1,
  assumption,
end

example: (P -> Q -> R) -> (P /\ Q -> R) :=
begin
  simp,
end

example: (P \/ Q -> R) -> (P -> R) /\ (Q -> R) :=
begin
  intros H,
  split,
  {
    intro H1,
    apply H,
    left,
    assumption,
  },
  {
    intro H2,
    apply H,
    right,
    assumption,
  },
end

example: P -> P /\ true :=
begin
  intros HP,
  split,
  {
    assumption
  },
  {
    apply true.intro,
  },
end

example: P \/ false -> P :=
begin
  intros H,
  cases H,
  {
    assumption
  },
  {
    apply (false.elim H),
  },
end

-- https://leanprover.github.io/logic_and_proof/classical_reasoning.html#:~:text=The%20principle%20is%20known%20as,em%20in%20the%20Lean%20library.
open classical

example: (P -> Q \/ R) -> (P -> Q) \/ (P -> R) :=
begin
  intros H,
  -- let H1:=(em P),
  cases (em (P -> Q)),
  {
    left,
    assumption,
  },
  {
    right,
    intros HP,
    specialize (H HP),
    cases H,
    {
      exfalso,
      apply h,
      intro,
      assumption,
    },
    {
      assumption,
    },
  }
end

example: P \/ ¬ P :=
begin
  apply classical.by_contradiction,
  intro H,
  apply H,
  right,
  intro HP,
  apply H,
  left,
  assumption,
end

end proplogic.

-- https://leanprover.github.io/theorem_proving_in_lean/quantifiers_and_equality.html
section firstorder.
  variables (X:Type) (P Q : X×X -> Prop)

  example:
      (forall x y, P (x,y) -> Q (y,x)) /\ 
      (forall x, P(x,x)) -> 
      forall y, Q (y,y) :=
  begin
    intros H1 x,
    cases H1 with H1 H2,
    specialize (H1 x x),
    apply H1,
    specialize (H2 x),
    assumption,
  end

  example:
      (forall x y, P (x,y) -> Q (y,x)) /\ 
      (forall x, P(x,x)) -> 
      forall y, Q (y,y) :=
  begin
    intros H1 x,
    cases H1 with H1 H2,
    apply H1,
    apply H2,
  end


def is_even (a : nat) := ∃ b, a = 2 * b

theorem even_plus_even {a b : nat}
  (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
exists.elim h1 (assume w1, assume hw1 : a = 2 * w1,
exists.elim h2 (assume w2, assume hw2 : b = 2 * w2,
  exists.intro (w1 + w2)
    (calc
      a + b = 2 * w1 + 2 * w2  : by rw [hw1, hw2]
        ... = 2*(w1 + w2)      : by rw mul_add)))

theorem even_plus_even2 {a b : nat}
  (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
match h1, h2 with
  ⟨w1, hw1⟩, ⟨w2, hw2⟩ := ⟨w1 + w2, by rw [hw1, hw2, mul_add]⟩
end

theorem even_plus_even3 {a b : nat}
  (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
begin
  cases h1 with w1 hw1,
  cases h2 with w2 hw2,
  existsi w1 + w2,
  rw [hw1, hw2, mul_add]
end


end firstorder.





#print function.surjective

variable {α : Type}

-- adapted from Pedro Minicz
-- which adapted a proof from ICL in Coq
-- hover over a tactic to see the explanation
lemma not_exists_surj : ¬ ∃ f : α → set α, function.surjective f :=
begin
  intro h,
  cases h with f hf,
  let s := {x | x ∉ f x},
  have hs : ∃ x, _ := hf s,
  cases hs with x hx,
  have : x ∈ s ↔ x ∈ f x, by rw hx,
  simp only [set.mem_set_of_eq] at this,
  simpa
end

prefix # := cardinal.mk

theorem cantor : #α < #(set α) :=
begin
  split,
  -- a is not larger than the powerset (smaller or equal)
  { -- show by injection into powerset (single element sets)
    let f : α → set α := λ x, {x},
    refine ⟨⟨f, _⟩⟩, 
    intros x₁ x₂ hx,
    simpa using hx },
  -- the powerset is strictly larger (not smaller or equal)
  { -- show no injective from powerset to set by
    -- contrapos: no surjective from set to powerset
    rintro ⟨⟨f, hf⟩⟩,
    refine not_exists_surj ⟨function.inv_fun f, _⟩,
    exact function.inv_fun_surjective hf }
end