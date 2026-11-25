-- Prove2me | Theorems.Thm_group_construction_exceeds_SCC_threshold
-- name    : group_construction_exceeds_SCC_threshold
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:00:14.345022+00:00
-- url     : https://prove2.me/theorems/9c9d893a-ac9d-4d61-a575-20ca25e75367
-- title:
--   group construction exceeds SCC threshold: group construction exceeds SCC threshold
-- statement:
--   The group construction exceeds SCC threshold construction uses the group construction exceeds SCC threshold property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/Solution.lean#L74-L85
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/Solution.lean#L74-L85

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

theorem group_construction_exceeds_SCC_threshold {G : Type*} [Group G] [Fintype G]
    (k : ℕ) (hk : 2 ≤ k) (f₁ f₂ f₃ : Finset (Fin (3 * k)) → G)
    (hPPP : ∀ A B C : Finset (Fin (3 * k)), A.card = k → B.card = k → C.card = k →
      (f₁ A * f₂ B * f₃ C = 1 ↔ Disjoint A B ∧ Disjoint A C ∧ Disjoint B C)) :
    (8 ^ k * (Nat.choose (3 * k) k) * (Nat.choose (2 * k) k) : ℚ) / 27 ^ k <
      Fintype.card G := by sorry
