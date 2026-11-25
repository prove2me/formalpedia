-- Prove2me | Theorems.Thm_group_constructions_cannot_refute_SCC
-- name    : group_constructions_cannot_refute_SCC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:00:41.053115+00:00
-- url     : https://prove2.me/theorems/c5b944ef-673d-4ff0-af68-fcab03e982d7
-- title:
--   group constructions cannot refute SCC: group constructions cannot refute SCC
-- statement:
--   The group constructions cannot refute SCC construction uses the group constructions cannot refute SCC property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/Solution.lean#L104-L126
-- source:
--   https://github.com/Eyali1001/scc-group-barrier/blob/6e572ed4367b37cfd89830f2fa99f4705d300c93/Solution.lean#L104-L126

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

theorem group_constructions_cannot_refute_SCC {G : Type*} [Group G] [Fintype G]
    (k m : ℕ) (hk : 2 ≤ k) (hm : 1 ≤ m)
    (f₁ f₂ f₃ : (Fin m → Finset (Fin (3 * k))) → G) (a b c : (Fin m → Finset (Fin (3 * k))) → ℤ)
    (hpart : ∀ A B C : Fin m → Finset (Fin (3 * k)),
      (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
      (∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) →
        f₁ A * f₂ B * f₃ C = 1 ∧ a A + b B + c C = 0)
    (hnon : ∀ A B C : Fin m → Finset (Fin (3 * k)),
      (∀ j, (A j).card = k) → (∀ j, (B j).card = k) → (∀ j, (C j).card = k) →
      ¬ (∀ j, Disjoint (A j) (B j) ∧ Disjoint (A j) (C j) ∧ Disjoint (B j) (C j)) →
        f₁ A * f₂ B * f₃ C = 1 → 0 < a A + b B + c C) :
    ((8 ^ k * (Nat.choose (3 * k) k) * (Nat.choose (2 * k) k) : ℚ) / 27 ^ k) ^ m <
      Fintype.card G := by sorry
