-- Prove2me | Theorems.Thm_mme_split_pair_product_mass_le
-- name    : mme_split_pair_product_mass_le
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T06:29:38.34098+00:00
-- url     : https://prove2.me/theorems/ac590379-b842-4e40-988e-5b9f9766dcbd
-- title:
--   Two coordinate weights bound total split mass
-- statement:
--   Any two distinct coordinates determine an admissible split. The total product of two nonnegative coordinate weights over splits is bounded by the product of their full coordinate masses, at every half-grade and parent shape. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Definitions.Def_mme_recursive_thin_split_data
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FinCases
open scoped BigOperators
open MME.RecursiveThinSplit

theorem mme_split_pair_product_mass_le {half : ℕ} {parent : Fin 3 → ℕ}
    (i j : Fin 3) (hij : i ≠ j)
    (p q : Fin (half + 1) → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hq : ∀ b, 0 ≤ q b) :
    (∑ c : Split half parent, p (c.val i) * q (c.val j)) ≤
      (∑ a, p a) * (∑ b, q b) := by sorry
