-- Prove2me | solution 1 for TropicalDequantization.tendsto_logSumExp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:47:07.070992+00:00
-- url     : https://prove2.me/submissions/e14e4ed0-25de-4784-b831-93f6bf32f2ae

-- Sol generated from Tropical/SocialChoice/Dequantization.lean
import Mathlib
import Definitions.Def_Tropical_SocialChoice_Dequantization
import Theorems.Thm_TropicalDequantization_logSumExp_sandwich
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








/-! ## Dequantized aggregators -/







open TropicalDequantization in
theorem solution{S : Finset ι} (hS : S.Nonempty) (a : ι → ℝ) :
    Filter.Tendsto (fun ε => logSumExp ε S a) (nhdsWithin 0 (Set.Ioi (0:ℝ)))
      (nhds (S.inf' hS a)) := by
  have hupper : Filter.Tendsto (fun _ : ℝ => S.inf' hS a) (nhdsWithin 0 (Set.Ioi (0:ℝ)))
      (nhds (S.inf' hS a)) := tendsto_const_nhds
  have hlower : Filter.Tendsto (fun ε : ℝ => S.inf' hS a - ε * Real.log S.card)
      (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (S.inf' hS a)) := by
    have : Filter.Tendsto (fun ε : ℝ => S.inf' hS a - ε * Real.log S.card)
        (nhds 0) (nhds (S.inf' hS a - 0 * Real.log S.card)) := by
      exact (tendsto_const_nhds.sub ((continuous_id.mul continuous_const).tendsto 0))
    simpa using this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (logSumExp_sandwich hS hε a).1
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (logSumExp_sandwich hS hε a).2
