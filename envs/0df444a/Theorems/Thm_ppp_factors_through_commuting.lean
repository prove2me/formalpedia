-- Prove2me | Theorems.Thm_ppp_factors_through_commuting
-- name    : ppp_factors_through_commuting
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:59:16.410047+00:00
-- url     : https://prove2.me/theorems/63ac632a-7a7d-5782-9476-830aedfe18cb
-- title:
--   ppp factors through commuting: ppp factors through commuting
-- statement:
--   The ppp factors through commuting construction uses the ppp factors through commuting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/Solution.lean#L37-L47
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/Solution.lean#L37-L47

module
public import Mathlib
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Numeric
public import Definitions.Def_SCCThm8_Degeneration
public import Definitions.Def_SCCThm8_PowerDegeneration
public import Definitions.Def_SCCGroupBarrier_Solution
set_option autoImplicit true
@[expose] public section
public section
open Finset

theorem ppp_factors_through_commuting {G : Type*} [Group G] (k : ℕ) (hk : 2 ≤ k)
    (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G)
    (hP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      Disjoint A B → Disjoint A C → Disjoint B C → f₁ A * f₂ B * f₃ C = 1) :
    ∃ g : Fin (3 * k) → G, (∀ i j, Commute (g i) (g j)) ∧
      ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
        f₁ A * f₂ B * f₃ C =
          ((List.finRange (3 * k)).map fun i =>
            g i ^ ((if i ∈ A then 1 else 0) + (if i ∈ B then 1 else 0) +
              (if i ∈ C then 1 else 0) - 1 : ℤ)).prod := by sorry
