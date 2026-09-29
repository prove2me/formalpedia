-- Prove2me | Definitions.Def_Tropical_SocialChoice_Dequantization
-- name    : Tropical_SocialChoice_Dequantization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:33:00.796703+00:00
-- url     : https://prove2.me/theorems/3fa45914-2312-40e6-943f-2caa3862025b
-- title:
--   Aether Catalog definitions — Tropical_SocialChoice_Dequantization
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.SocialChoice.Dequantization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/SocialChoice/Dequantization.lean by skeleton subtraction
import Mathlib
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

namespace TropicalDequantization

open Finset

variable {ι : Type*}

/-- The log-sum-exp (softmin) smoothing of the tropical minimum at scale `ε`. -/
noncomputable def logSumExp (ε : ℝ) (S : Finset ι) (a : ι → ℝ) : ℝ :=
  -ε * Real.log (∑ i ∈ S, Real.exp (-(a i) / ε))







/-! ## Dequantized aggregators -/

/-- The tropical aggregator with support `S` and weights `δ`. -/
noncomputable def tropAgg (S : Finset ι) (hS : S.Nonempty) (δ : ι → ℝ) : (ι → ℝ) → ℝ :=
  fun x => S.inf' hS fun i => x i + δ i

/-- Its classical (positive, smooth) dequantization at scale `ε`. -/
noncomputable def dequant (ε : ℝ) (S : Finset ι) (δ : ι → ℝ) : (ι → ℝ) → ℝ :=
  fun x => logSumExp ε S fun i => x i + δ i




end TropicalDequantization


