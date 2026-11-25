-- Prove2me | Theorems.Thm_exists_tendsto_rpow_inv_of_le_mul_const
-- name    : exists_tendsto_rpow_inv_of_le_mul_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:25:26.817999+00:00
-- url     : https://prove2.me/theorems/be7f15d5-8022-478a-a822-85069409ccc7
-- title:
--   exists tendsto rpow inv of le mul const: exists tendsto rpow inv of le mul const
-- statement:
--   **Submultiplicative sequences with a bounded defect.** If `a n > 0` for `n ≠ 0`,
--   `a (m + n) ≤ K * a m * a n` for all `m, n` with `K > 0`, and `a n ≥ c ^ n` for some `c > 0`, then
--   `a n ^ (1 / n) → L` for some `L > 0` with `L ^ n ≤ K * a n` for every `n`. (Positivity of `a 0`
--   follows from the hypotheses.)
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/BoundedDefect.lean#L93-L116
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/BoundedDefect.lean#L93-L116

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_BoundedDefect
set_option autoImplicit true
@[expose] public section
public section
open Filter
open scoped Topology

theorem exists_tendsto_rpow_inv_of_le_mul_const {a : ℕ → ℝ} {K : ℝ} (ha : ∀ n, n ≠ 0 → 0 < a n)
    (hK : 0 < K) (h : ∀ m n, a (m + n) ≤ K * a m * a n) (hc : ∃ c > 0, ∀ n : ℕ, c ^ n ≤ a n) :
    ∃ L > 0, Tendsto (fun n ↦ a n ^ (n : ℝ)⁻¹) atTop (𝓝 L) ∧ ∀ n : ℕ, L ^ n ≤ K * a n := by sorry
