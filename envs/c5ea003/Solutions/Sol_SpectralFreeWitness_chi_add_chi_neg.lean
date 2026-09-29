-- Prove2me | solution 1 for SpectralFreeWitness.chi_add_chi_neg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:41:43.338563+00:00
-- url     : https://prove2.me/submissions/9eada082-3b3c-4569-bc6c-2c276883a5d4

-- Sol generated from Speculative/AutoResearch/SpectralFreeWitnessWalk.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitnessWalk
/-
# The dyadic diffusion operator: heat kernel = return probability

`Algebra.SpectralFreeWitness` defines the heat-kernel value `p_n(e)` *spectrally*,
as `(1/r) ∑_k μ_k^n`.  This file shows that this spectral definition is the genuine
`n`-step return probability of the half-lazy lacunary dyadic random walk, by

* introducing the diffusion (transition) operator
  `W f (x) = f x / 2 + (∑_{t ≤ M} (f (x + 2^t) + f (x - 2^t))) / (4 (M+1))`
  acting on `r`-periodic functions on the cycle `Z/rZ` (realised as functions `ℤ → ℂ`),
* proving that the additive characters `χ_k (x) = e^{2πi k x / r}` are eigenvectors
  of `W` with eigenvalues exactly the `lazyEigen r M k` of the spectral file
  (`walkStep_chi`),
* proving the discrete Fourier expansion of the periodic delta function
  (`sum_chi`: character orthogonality on `Z/rZ`),
* concluding `W^[n] δ (0) = p_n(e)` (`walk_return_eq_heatReturn`), and hence the
  fully operational statement of heat-kernel order recovery
  (`walk_recovers_order`): the *measured* return probability of the diffusion,
  after `8 (M+1)^2` steps, determines the order `r` by a single rounding.

No `sorry`, no `native_decide`.
-/


open SpectralFreeWitness

open Finset Real

/-! ## 1. The additive characters of the cycle -/





/-! ## 2. The diffusion operator -/








/-! ## 3. Fourier expansion of the delta function -/



/-! ## 4. The return probability equals the spectral heat kernel -/




open SpectralFreeWitness in
theorem solution(r k : ℕ) (m : ℤ) :
    chi r k m + chi r k (-m) = 2 * ((Real.cos (2 * π * ((k : ℝ) * (m : ℝ)) / r) : ℝ) : ℂ) := by
  have hz : (2 * π * Complex.I * ((k : ℂ) * (m : ℂ)) / r)
      = ((2 * π * ((k : ℝ) * (m : ℝ)) / r : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hz' : (2 * π * Complex.I * ((k : ℂ) * ((-m : ℤ) : ℂ)) / r)
      = -(((2 * π * ((k : ℝ) * (m : ℝ)) / r : ℝ) : ℂ) * Complex.I) := by
    push_cast
    ring
  simp only [chi, hz, hz']
  rw [Complex.exp_mul_I, ← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  rw [Complex.ofReal_cos]
  ring
