-- Prove2me | Theorems.Thm_exists_tendsto_div_of_abs_sub_le
-- name    : exists_tendsto_div_of_abs_sub_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:25:23.671942+00:00
-- url     : https://prove2.me/theorems/4f0f76ce-6dd9-59b4-be9e-a293ac8d1e6f
-- title:
--   exists tendsto div of abs sub le: exists tendsto div of abs sub le
-- statement:
--   **Almost additive sequences.** If `|u (m + n) - u m - u n| ≤ C` for all `m, n`, then
--   `u n / n → L` for some `L` with `|u n - n * L| ≤ C` for every `n`.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/BoundedDefect.lean#L69-L87
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/BoundedDefect.lean#L69-L87

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_BoundedDefect
set_option autoImplicit true
@[expose] public section
public section
open Filter
open scoped Topology

theorem exists_tendsto_div_of_abs_sub_le {u : ℕ → ℝ} {C : ℝ}
    (h : ∀ m n, |u (m + n) - u m - u n| ≤ C) :
    ∃ L, Tendsto (fun n ↦ u n / n) atTop (𝓝 L) ∧ ∀ n : ℕ, |u n - n * L| ≤ C := by sorry
