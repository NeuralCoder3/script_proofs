import Mathlib.Data.Set.Basic
import Mathlib.Tactic

theorem t4_17 (α : Type) (A B : Set α) :
  A = B ↔ A ⊆ B ∧ B ⊆ A := by
  constructor
  · intro h
    constructor
    · intro x hx
      rw [h] at hx
      assumption
    · intro x hx
      rw [<- h] at hx
      assumption
  · intro ⟨h1, h2⟩
    ext x
    constructor
    · intro hx
      exact h1 hx
    · intro hx
      exact h2 hx

theorem t4_18 (α : Type) (A B : Set α) (P Q : α → Prop)
  (HA : A = {x | P x}) (HB : B = {x | Q x}) :
  A = B ↔ ∀ x, P x ↔ Q x := by
  constructor
  · intro h
    intro x
    rw [HA,HB] at h
    constructor
    · intro hx
      change (x ∈ {x | Q x})
      rw [<- h]
      assumption
    · intro hx
      change (x ∈ {x | P x})
      rw [h]
      assumption
  · intro h
    rw [HA,HB]
    ext x
    constructor
    · intro hx
      apply (h x).1
      assumption
    · intro hx
      apply (h x).2
      assumption

theorem t4_12 (α : Type) (A B : Set α) :
  A \ B = A ∩ Bᶜ := by
  ext x
  constructor
  · intro H
    obtain ⟨HA, HB⟩ := H
    constructor
    · exact HA
    · intro hx_not_in_B
      exact (HB hx_not_in_B)
  · intro H
    obtain ⟨HA, HB⟩ := H
    constructor
    · assumption
    · intro hx_not_in_B
      apply HB
      assumption


-- Theorem 4.27
theorem comm_union (α : Type) (A B : Set α) :
  A ∪ B = B ∪ A := by
  ext x
  constructor
  · intro hx
    obtain HA | HB := hx
    · right;assumption
    · left;assumption
  · intro H
    obtain HA | HB := H
    · right;assumption
    · left;assumption

theorem comm_intersect (α : Type) (A B : Set α) :
  A ∩ B = B ∩ A := by
  ext x
  constructor
  · intro H
    obtain ⟨HA, HB⟩ := H
    constructor<;>assumption
  · intro H
    obtain ⟨HB, HA⟩ := H
    constructor<;>assumption

-- others are same lift of bool/prop logic

-- skipped 4.28 -

def f (x : ℕ) : ℤ :=
  if x%2=0 then (x / 2 : ℕ) else -((x+1)/2 : ℕ)
  -- if x%2=0 then (Nat.div x 2) else -(Nat.div (x+1) 2)
  -- if x%2=0 then (@HDiv.hDiv ℕ ℕ ℕ instHDiv x 2) else -((@HDiv.hDiv ℕ ℕ ℕ instHDiv (x+1) 2))

theorem t4_84:
  Function.Bijective f := by
  -- left total by construction
  constructor
  · -- injective
    intro a₁ a₂ H
    by_cases h₁ : a₁%2=0
    . by_cases h₂ : a₂%2=0
      . simp [f, h₁, h₂] at H
        apply_fun (λ x => 2*x) at H
        change ((↑(2 * (a₁ / 2)):ℤ) = (↑(2 * (a₂ / 2)):ℤ)) at H
        rw [Nat.two_mul_div_two_of_even, Nat.two_mul_div_two_of_even] at H
        swap;apply Nat.even_iff.2;assumption
        swap;apply Nat.even_iff.2;assumption
        injection H
      . simp [f, h₁, h₂] at H
        apply_fun (λ x => 2*x) at H
        simp at H
        exfalso
        change ((↑(2 * (a₁ / 2)):ℤ) = (-((↑(2 * ((a₂+1) / 2))):ℤ))) at H
        rw [Nat.two_mul_div_two_of_even] at H
        swap;apply Nat.even_iff.2;assumption
        rw [Nat.two_mul_div_two_of_even] at H
        swap;sorry
        sorry
    . sorry
  · -- surjective
    intro b
    by_cases h : b%2=0
    . use 2*b
      simp [f, h]
    . use 2*(-b-1)+1
      simp [f, h]
