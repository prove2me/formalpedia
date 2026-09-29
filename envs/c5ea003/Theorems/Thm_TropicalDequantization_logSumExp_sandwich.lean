-- Prove2me | Theorems.Thm_TropicalDequantization_logSumExp_sandwich
-- name    : TropicalDequantization.logSumExp_sandwich
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T08:39:33.614766+00:00
-- url     : https://prove2.me/theorems/90b127d6-76ed-4964-9239-88eaf8a55e82
-- title:
--   Explicit dequantization sandwich.
-- statement:
--   **Explicit dequantization sandwich.**
--
--   ```lean
--   theorem TropicalDequantization.logSumExp_sandwich{S : Finset ι} (hS : S.Nonempty) {ε : ℝ} (hε : 0 < ε) (a : ι → ℝ) :
--       S.inf' hS a - ε * Real.log S.card ≤ logSumExp ε S a ∧ logSumExp ε S a ≤ S.inf' hS a := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Tropical/SocialChoice/Dequantization.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Tropical/SocialChoice/Dequantization.lean#L60

-- Thm stub generated from Tropical/SocialChoice/Dequantization.lean
import Mathlib
import Definitions.Def_Tropical_SocialChoice_Dequantization
/-
# Maslov dequantization of tropical aggregators

A second bridge, this time between **tropical (min-plus) aggregation** and
**classical analysis**: the log-sum-exp ("softmin") family

`F_ε x = -ε · log ( Σ_{i ∈ S} exp (-(x i + δ i)/ε) )`

is a family of genuinely classical, positive, smooth aggregators, and it
converges to the tropical aggregator `x ↦ min_{i ∈ S} (x i + δ i)` as `ε ↓ 0`.

Main results.

* `logSumExp_sandwich` : the two-sided, fully explicit estimate
  `A - ε log |S| ≤ -ε log Σ exp(-a i/ε) ≤ A`, where `A = min_{i ∈ S} a i`.
* `tendsto_logSumExp` : the resulting convergence as `ε ↓ 0`.
* `dequant_sub_trop_abs_le` : the dequantized aggregators converge to the
  tropical aggregator *uniformly in the profile*, with rate `ε log |S|`.
* `dequant_eq_trop_iff_card_eq_one` : the dequantization is *exact* (there is no
  deformation at all) precisely when the tropical support is a singleton, i.e.
  precisely for dictatorships.  This is the "dequantization stability of
  decisive coalitions" phenomenon in sharp form.
-/

open TropicalDequantization

open Finset

variable {ι : Type*}

theorem TropicalDequantization.logSumExp_sandwich{S : Finset ι} (hS : S.Nonempty) {ε : ℝ} (hε : 0 < ε) (a : ι → ℝ) :
    S.inf' hS a - ε * Real.log S.card ≤ logSumExp ε S a ∧ logSumExp ε S a ≤ S.inf' hS a := by sorry
