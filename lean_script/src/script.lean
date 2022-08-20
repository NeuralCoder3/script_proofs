-- import tactic.fresh_name
-- import tactic
-- import tactic.interactive
open lean
open lean.parser
open interactive interactive.types expr

variables (P Q : Prop)

example: (P /\ Q -> Q /\ P) :=
begin
    intro H,
    cases H,
    split,
    repeat { assumption },
end

example (p q : Prop) : p ∧ q → q ∧ p :=
assume ⟨h₁, h₂⟩,
and.intro (by assumption) (by assumption)

-- namespace tactic

-- meta def ImplIntro := tactic.intro1
meta def AndElim (H) := 
  do 
  tactic.cases H,
  tactic.intro1,
  tactic.intro1
-- meta def ImplIntro : tactic expr := 
-- meta def ImplIntro (n:option (parse ident) := none) : tactic expr :=
-- meta def ImplIntro (n:parse ident) : tactic expr :=
-- meta def ImplIntro (n:parse ident) : tactic expr :=
  -- tactic.intro n
  -- interactive.intro
-- meta def ImplIntro (n:option (parse ident) := none) : tactic expr :=
-- meta def ImplIntro := interactive.intro
-- notation `ImplIntro` := intro
-- meta def ImplIntro (n:option string := none) : tactic expr :=
-- match n with
-- | none :=
--   do 
--     h <- get_unused_name `H,
--     tactic.intro h
-- | (some h) := tactic.intro (mk_simple_name h)
-- end
  -- do 
  --   h <- get_unused_name `H,
  --   tactic.intro h

-- meta def AndElim (p : parse texpr) : tactic _ :=
-- meta def AndElim (p : parse texpr) : tactic _ :=
-- meta def AndElim (p : expr) : tactic _ :=
  -- i_to_expr p >>= tactic.cases
  -- i_to_expr p >>= tactic.destruct
-- meta def AndElim (p : parse texpr) : tactic unit :=
-- i_to_expr p >>= tactic.destruct
  -- i_to_expr p >>= tactic.destruct
  -- tactic.cases p
-- do 
--   tactic.destruct H,
--   e1 <- ImplIntro,
--   e2 <- ImplIntro,
--   return e1
-- meta def AndElim H : tactic expr :=

namespace tactic
namespace interactive
open interactive interactive.types expr
    -- meta def ImplIntro := tactic.interactive.intro
  meta def ImplIntro : parse (optional ident) → tactic unit := intro
  -- | none     := propagate_tags (intro1 >> skip)
  -- | (some h) := propagate_tags (tactic.intro h >> skip)

  meta def AndElim (H:parse texpr) : tactic unit :=
    do 
    -- destruct H,
    -- h <- i_to_expr_for_apply H,
    -- l <- i_to_expr (and.elim h),
    -- apply l,
    -- apply (pexpr.of_expr (and.elim)),
    apply (to_pexpr (and.elim)),
    ImplIntro none,
    ImplIntro none

  meta def AndIntro := apply 

end interactive
end tactic

example: (P /\ Q -> Q /\ P) :=
begin
  -- ImplIntro `M,
  -- ImplIntro,
  ImplIntro H,
  -- ImplIntro H,
  -- intro,
  -- intro H,
  -- show P,
  -- intro H,
  -- AndElim H,
  AndIntro (and.elim H),
  -- AndElim H,
  -- destruct H,
  -- cases H,
  sorry,
  -- destruct H,
  -- trace H,
  -- AndElim H,
  -- apply and.intro,
end
