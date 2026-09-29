-- Prove2me | solution 1 for LatticeEnumerator.integral_stepFun
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:07:25.138774+00:00
-- url     : https://prove2.me/submissions/93fa9890-d7d8-4c86-905f-00dc11e4e04a

-- Sol generated from Cryptography/LatticePointFourier.lean
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator
import Definitions.Def_Cryptography_LatticePointFourier
import Theorems.Thm_LatticeEnumerator_dilLattice_finite
import Theorems.Thm_LatticeEnumerator_measurableSet_cube
import Theorems.Thm_LatticeEnumerator_mem_dilLattice
import Theorems.Thm_LatticeEnumerator_stepFun_eq_sum
import Theorems.Thm_LatticeEnumerator_volume_cube

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


lemma weightedSum_eq_finsetSum {P : Set (Fin d → ℝ)} {t : ℝ} (hfin : (dilLattice P t).Finite)
    (g : (Fin d → ℝ) → ℂ) :
    weightedSum P t g = ∑ k ∈ hfin.toFinset, g (fun i => (k i : ℝ) / t) := by
  rw [weightedSum, ← finsum_mem_coe_finset]
  simp [hfin.coe_toFinset]











open LatticeEnumerator in
theorem solution{P : Set (Fin d → ℝ)} (hb : Bornology.IsBounded P) {t : ℝ} (ht : 0 < t)
    (g : (Fin d → ℝ) → ℂ) :
    ∫ x, (approxSet P t).indicator (fun x => g (floorMap t x)) x
      = ((t ^ d)⁻¹ : ℝ) • weightedSum P t g := by
  have hfin := dilLattice_finite hb ht
  have hcube : ∀ k : Fin d → ℤ, (volume (cube t k)).toReal = (t ^ d)⁻¹ := by
    intro k
    rw [volume_cube ht, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity), div_pow,
      one_pow]
    ring
  have hint : ∀ k : Fin d → ℤ,
      Integrable ((cube t k).indicator (fun _ => g (fun i => (k i : ℝ) / t))) volume := by
    intro k
    rw [integrable_indicator_iff (measurableSet_cube t k)]
    refine integrableOn_const ?_
    rw [volume_cube ht]
    exact (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne
  calc ∫ x, (approxSet P t).indicator (fun x => g (floorMap t x)) x
      = ∫ x, ∑ k ∈ hfin.toFinset,
          (cube t k).indicator (fun _ => g (fun i => (k i : ℝ) / t)) x := by
        exact integral_congr_ae (Filter.Eventually.of_forall (stepFun_eq_sum ht hfin g))
    _ = ∑ k ∈ hfin.toFinset,
          ∫ x, (cube t k).indicator (fun _ => g (fun i => (k i : ℝ) / t)) x :=
        integral_finset_sum _ fun k _ => hint k
    _ = ∑ k ∈ hfin.toFinset, ((t ^ d)⁻¹ : ℝ) • g (fun i => (k i : ℝ) / t) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_indicator_const _ (measurableSet_cube t k), measureReal_def, hcube k]
    _ = ((t ^ d)⁻¹ : ℝ) • weightedSum P t g := by
        rw [weightedSum_eq_finsetSum hfin, Finset.smul_sum]
