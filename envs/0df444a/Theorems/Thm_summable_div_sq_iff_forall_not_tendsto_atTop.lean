-- Prove2me | Theorems.Thm_summable_div_sq_iff_forall_not_tendsto_atTop
-- name    : summable_div_sq_iff_forall_not_tendsto_atTop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:33:21.541714+00:00
-- url     : https://prove2.me/theorems/047ecef0-2285-56b5-af76-53718f02029d
-- title:
--   summable div sq iff forall not tendsto at Top: summable div sq iff forall not tendsto at Top
-- statement:
--   **Sharpness of de Bruijn–Erdős.** For a nonnegative monotone `f`, `∑ f n / n ^ 2 < ∞` if and
--   only if no sequence with `u (m + n) ≤ u m + u n + f (m + n)` for all `m, n` has `u n / n → ∞`.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Sharpness.lean#L123-L134
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Sharpness.lean#L123-L134

module
public import Definitions.Def_Fekete_DeBruijnErdos
public import Definitions.Def_Fekete_Sharpness
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Finset
open scoped Topology
open NearlySubadditive

theorem summable_div_sq_iff_forall_not_tendsto_atTop (hf0 : 0 ≤ f) (hf : Monotone f) :
    (Summable fun n : ℕ ↦ f n / (n : ℝ) ^ 2) ↔
      ∀ u : ℕ → ℝ, (∀ m n, u (m + n) ≤ u m + u n + f (m + n)) →
        ¬ Tendsto (fun n ↦ u n / n) atTop atTop := by sorry
