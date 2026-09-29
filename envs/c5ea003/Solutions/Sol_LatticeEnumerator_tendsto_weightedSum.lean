-- Prove2me | solution 1 for LatticeEnumerator.tendsto_weightedSum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:09:32.866652+00:00
-- url     : https://prove2.me/submissions/44c5e2b5-6633-46ca-8a6b-bd396f44cbc0

-- Sol generated from Cryptography/LatticePointFourier.lean
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator
import Definitions.Def_Cryptography_LatticePointFourier
import Theorems.Thm_LatticeEnumerator_approxSet_subset_closedBall
import Theorems.Thm_LatticeEnumerator_dist_floorMap_le
import Theorems.Thm_LatticeEnumerator_eventually_mem_approxSet_iff
import Theorems.Thm_LatticeEnumerator_integral_stepFun
import Theorems.Thm_LatticeEnumerator_measurableSet_approxSet

/-!
# Recovering the Fourier transform of an indicator from lattice sums

This file develops the *weighted* form of the Gauss–Weyl counting theorem of
`Cryptography.LatticePointEnumerator`: for a bounded Jordan measurable set `P ⊆ ℝ^d` and a
bounded continuous weight `g`,

`t^{-d} · Σ_{k ∈ tP ∩ ℤ^d} g(k/t) → ∫ 1_P · g`  as `t → ∞`.

Specialising `g` to a character `x ↦ exp(-2πi⟨ξ, x⟩)` shows that the *Fourier transform of the
indicator function* of `P` is recovered, at every frequency `ξ`, as a limit of exponential sums
over the counted lattice points.  This is the analytic content of the "periodic point-counting
function whose Fourier coefficients recover the Fourier transform of the indicator function"
used in the paper.

## Main results

* `LatticeEnumerator.integral_stepFun` : the exact identity
  `∫ 1_{A_t}(x) g(⌊tx⌋/t) dx = t^{-d} Σ_{k ∈ tP ∩ ℤ^d} g(k/t)`.
* `LatticeEnumerator.tendsto_weightedSum` : the weighted counting theorem.
* `LatticeEnumerator.tendsto_fourierSum` : recovery of `∫ 1_P(x) e^{-2πi⟨ξ,x⟩} dx` from the
  lattice exponential sums.
* `LatticeEnumerator.weightedSum_one_eq_dilCount` : consistency check — for `g = 1` the weighted
  theorem specialises to `L_P(t)/t^d → vol P`.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology Complex

open LatticeEnumerator

variable {d : ℕ}





/-- The rounding maps converge pointwise to the identity as `t → ∞`. -/
lemma tendsto_floorMap (x : Fin d → ℝ) :
    Tendsto (fun t : ℝ => floorMap t x) atTop (𝓝 x) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun t => dist_nonneg)
    (g := fun t : ℝ => 1 / t) ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht using dist_floorMap_le ht x
  · simpa [one_div] using tendsto_inv_atTop_zero








open LatticeEnumerator in
theorem solution{P : Set (Fin d → ℝ)} (hb : Bornology.IsBounded P)
    (hfr : volume (frontier P) = 0) {g : (Fin d → ℝ) → ℂ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ x, ‖g x‖ ≤ C) :
    Tendsto (fun t : ℝ => ((t ^ d)⁻¹ : ℝ) • weightedSum P t g) atTop
      (𝓝 (∫ x, P.indicator g x)) := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hb
  have hC0 : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  set bound : (Fin d → ℝ) → ℝ := (closedBall (0 : Fin d → ℝ) (R + 1)).indicator fun _ => C
    with hbound
  have key : Tendsto (fun t : ℝ => ∫ x, (approxSet P t).indicator (fun x => g (floorMap t x)) x)
      atTop (𝓝 (∫ x, P.indicator g x)) := by
    refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hmeas : Measurable fun x : Fin d → ℝ => g (floorMap t x) := by
        refine hg.measurable.comp ?_
        refine measurable_pi_lambda _ fun i => ?_
        show Measurable fun x : Fin d → ℝ => ((⌊t * x i⌋ : ℤ) : ℝ) / t
        fun_prop
      exact (hmeas.indicator (measurableSet_approxSet hb ht)).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
      filter_upwards with x
      have hsub := approxSet_subset_closedBall hR ht
      by_cases hx : x ∈ approxSet P t
      · rw [Set.indicator_of_mem hx, hbound, Set.indicator_of_mem (hsub hx)]
        exact hC _
      · rw [Set.indicator_of_notMem hx, hbound, norm_zero]
        exact Set.indicator_nonneg (fun _ _ => hC0) x
    · rw [hbound, integrable_indicator_iff measurableSet_closedBall]
      exact integrableOn_const measure_closedBall_lt_top.ne
    · have hae : ∀ᵐ x : (Fin d → ℝ), x ∉ frontier P := measure_eq_zero_iff_ae_notMem.1 hfr
      filter_upwards [hae] with x hx
      have hev := eventually_mem_approxSet_iff (P := P) hx
      by_cases hxP : x ∈ P
      · rw [Set.indicator_of_mem hxP]
        have hlim : Tendsto (fun t : ℝ => g (floorMap t x)) atTop (𝓝 (g x)) :=
          (hg.tendsto x).comp (tendsto_floorMap x)
        refine hlim.congr' ?_
        filter_upwards [hev] with t ht
        rw [Set.indicator_of_mem (ht.2 hxP)]
      · rw [Set.indicator_of_notMem hxP]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with t ht
        rw [Set.indicator_of_notMem (fun hmem => hxP (ht.1 hmem))]
  refine key.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact integral_stepFun hb ht g
