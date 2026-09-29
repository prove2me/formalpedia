-- Prove2me | solution 1 for SpectralFreeWitness.heatReturn_ge_two_terms
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:50:49.221799+00:00
-- url     : https://prove2.me/submissions/3d992cd9-f834-48b4-9fff-4c02fe686a87

-- Sol generated from Speculative/AutoResearch/SpectralFreeWitnessLower.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
import Theorems.Thm_SpectralFreeWitness_lazyEigen_nonneg
import Theorems.Thm_SpectralFreeWitness_lazyEigen_zero
/-
# A matching lower bound: the diffusion really needs `Θ((log N)²)` steps

`Algebra.SpectralFreeWitness` proves that `n = 8 (M+1)²` half-lazy diffusion steps
suffice for exact order recovery.  Here we prove the converse for the extremal
Mersenne cycle `r = 2^M - 1`: if `154 n ≤ M (M+1)` then the rounding **fails**,

  `round (1 / p_n(e)) ≠ r`,

so the quadratic step count is not an artefact of the analysis — the lacunary dyadic
diffusion genuinely needs `Ω((log N)²)` steps.  Together with the upper bound this
pins the diffusion time of the spectral free-witness at `Θ((log N)²)`.

Ingredients:

* `exp_neg_two_mul_le_one_sub` — the elementary bound `e^{-2δ} ≤ 1 - δ` for `δ ≤ 1/2`
  (the reverse of the usual `1 - δ ≤ e^{-δ}`), which converts the sharpness bound on
  the top eigenvalue into a lower bound on its `n`-th power.
* `lazyEigen_mersenne_ge` — `μ₁ ≥ 1 - 53/(M+1)` from the sharpness result.
* `heatReturn_ge_two_terms` — dropping all but the two leading spectral terms.

No `sorry`, no `native_decide`.
-/


open SpectralFreeWitness

open Finset Real






open SpectralFreeWitness in
theorem solution(r M n : ℕ) (hr : 2 ≤ r) :
    (1 + (lazyEigen r M 1) ^ n) / (r : ℝ) ≤ heatReturn r M n := by
  have hr0 : (0 : ℝ) < r := by positivity
  have hrpos : 0 < r := by omega
  have h0 : 0 ∈ range r := mem_range.mpr (by omega)
  have h1 : (1 : ℕ) ∈ (range r).erase 0 := by
    rw [Finset.mem_erase, mem_range]
    exact ⟨by omega, by omega⟩
  have hsplit : ∑ k ∈ range r, (lazyEigen r M k) ^ n
      = (lazyEigen r M 0) ^ n + ∑ k ∈ (range r).erase 0, (lazyEigen r M k) ^ n :=
    (Finset.add_sum_erase _ _ h0).symm
  have hsplit2 : ∑ k ∈ (range r).erase 0, (lazyEigen r M k) ^ n
      = (lazyEigen r M 1) ^ n + ∑ k ∈ ((range r).erase 0).erase 1, (lazyEigen r M k) ^ n :=
    (Finset.add_sum_erase _ _ h1).symm
  have hrest : 0 ≤ ∑ k ∈ ((range r).erase 0).erase 1, (lazyEigen r M k) ^ n :=
    Finset.sum_nonneg fun i _ => pow_nonneg (lazyEigen_nonneg _ _ _) _
  rw [heatReturn, div_le_div_iff_of_pos_right hr0, hsplit, hsplit2,
    lazyEigen_zero r M, one_pow]
  linarith
