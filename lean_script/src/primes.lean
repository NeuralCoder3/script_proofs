import data.nat.prime
-- lia in coq
import tactic.linarith 

open nat

-- useful tactics for in between
-- library_search
--   quick look up if solved by lemma
-- suggest
--   suggest a lemma to refine the goal
-- show_term {}
--   short term of proof


-- longer proof with comments
-- short one below
theorem inf_prime:
∀ n, exists p > n, prime p := 
begin
  intros n,
  -- idea: smallest factor of n!+1 is such a prime
  let m := fact n + 1,
  let p := min_fac m,

  have prime_p : prime p := begin
    -- a factor (of anything ≠ 1) is a prime 
    apply min_fac_prime,
    -- m is not 1 becuase n! ≥ 1 
    -- +1 ≥ 2 
    have:= fact_pos n,
    linarith,
  end,

  use p,
  split,
  {
    -- why is p > n:
    -- if p would be smaller, 
    by_contradiction,
    have hₐ: p ≤ n := by linarith,
    -- it would divide n!
    have hₙ: p ∣ fact n := 
    begin
      -- smaller number divide factorial
      apply dvd_fact,
      { -- ≠ 0
        apply min_fac_pos,
      },
      { -- ≤ n
        exact hₐ,
      },
    end,
    -- we also now by its construction that p ∣ n! + 1
    have hₘ: p ∣ m := min_fac_dvd m,
    -- now that p divides n! and n!+1, it has to divide 1
    -- (.mp means: take left to right side of equivalence (mpr for other))
    have h₁: p ∣ 1 := (nat.dvd_add_right hₙ).mp hₘ,
    -- but p is a prime, so it can't divide 1
    exact prime.not_dvd_one prime_p h₁,
  },
  {
    exact prime_p,
  }

end


theorem inf_prime_short:
∀ n, ∃ p ≥ n, prime p := 
begin
  intros n,
  -- idea: smallest factor of n!+1 is such a prime
  let m := fact n + 1,
  let p := min_fac m,

  have prime_p : prime p := 
  begin
    refine min_fac_prime _,
    have : fact n > 0 := fact_pos n,
    linarith,
  end,

  use p,
  split,
  { 
    by_contradiction,
    have h₁ : p ∣ fact n + 1 := min_fac_dvd m,
    have h₂ : p ∣ fact n := 
    begin
      refine prime_p.dvd_fact.mpr _,
      exact le_of_not_ge a
    end,
    have h : p ∣ 1 := (nat.dvd_add_right h₂).mp h₁, 
    exact prime.not_dvd_one prime_p h,
   },
  { exact prime_p },

end