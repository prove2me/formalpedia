-- Prove2me | solution 1 for SpectralFreeWitness.exp_neg_two_mul_le_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:43:17.212786+00:00
-- url     : https://prove2.me/submissions/2ec81fdd-e24f-4359-aa30-3e67336a1521

-- Sol generated from Speculative/AutoResearch/SpectralFreeWitnessLower.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
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
theorem solution(δ : ℝ) (h0 : 0 ≤ δ) (h1 : δ ≤ 1 / 2) :
    Real.exp (-(2 * δ)) ≤ 1 - δ := by
  have hexp : (1 : ℝ) + 2 * δ ≤ Real.exp (2 * δ) := by
    have := Real.add_one_le_exp (2 * δ)
    linarith
  have hpos : (0 : ℝ) < 1 + 2 * δ := by linarith
  have hstep : Real.exp (-(2 * δ)) ≤ 1 / (1 + 2 * δ) := by
    rw [Real.exp_neg, inv_eq_one_div]
    exact one_div_le_one_div_of_le hpos hexp
  have hfrac : 1 / (1 + 2 * δ) ≤ 1 - δ := by
    rw [div_le_iff₀ hpos]
    nlinarith
  linarith
