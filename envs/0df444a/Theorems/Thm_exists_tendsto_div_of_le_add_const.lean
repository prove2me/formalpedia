-- Prove2me | Theorems.Thm_exists_tendsto_div_of_le_add_const
-- name    : exists_tendsto_div_of_le_add_const
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:25:26.907825+00:00
-- url     : https://prove2.me/theorems/dce27441-8558-480b-b2b9-cc1ebaeec237
-- title:
--   exists tendsto div of le add const: exists tendsto div of le add const
-- statement:
--   **Fekete's lemma with a bounded defect.** If `u (m + n) ≤ u m + u n + C` for all `m, n` and
--   `u n / n` is bounded below, then `u n / n → L` for some `L` with `n * L - C ≤ u n` for all `n`.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/BoundedDefect.lean#L47-L65
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/BoundedDefect.lean#L47-L65

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_BoundedDefect
set_option autoImplicit true
@[expose] public section
public section
open Filter
open scoped Topology

theorem exists_tendsto_div_of_le_add_const {u : ℕ → ℝ} {C : ℝ}
    (h : ∀ m n, u (m + n) ≤ u m + u n + C) (hbdd : BddBelow (Set.range fun n ↦ u n / n)) :
    ∃ L, Tendsto (fun n ↦ u n / n) atTop (𝓝 L) ∧ ∀ n : ℕ, n * L - C ≤ u n := by sorry
