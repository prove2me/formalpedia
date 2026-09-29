-- Prove2me | solution 1 for SpectralFreeWitness.walkStep_chi
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:13:29.2231+00:00
-- url     : https://prove2.me/submissions/b033e103-3524-43dd-97a6-89fa79fc7934

-- Sol generated from Speculative/AutoResearch/SpectralFreeWitnessWalk.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitnessWalk
import Theorems.Thm_SpectralFreeWitness_chi_add_chi_neg
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


lemma chi_add (r k : ℕ) (x y : ℤ) : chi r k (x + y) = chi r k x * chi r k y := by
  simp only [chi, ← Complex.exp_add]
  congr 1
  push_cast
  ring



/-! ## 2. The diffusion operator -/








/-! ## 3. Fourier expansion of the delta function -/



/-! ## 4. The return probability equals the spectral heat kernel -/




open SpectralFreeWitness in
theorem solution(r M k : ℕ) :
    walkStep M (chi r k) = fun x => ((lazyEigen r M k : ℝ) : ℂ) * chi r k x := by
  funext x
  have hMne : ((M : ℂ) + 1) ≠ 0 := by
    have hc : ((M : ℂ) + 1) = ((M + 1 : ℕ) : ℂ) := by push_cast; ring
    rw [hc, Nat.cast_ne_zero]
    omega
  have hterm : ∀ t ∈ range (M + 1), chi r k (x + 2 ^ t) + chi r k (x - 2 ^ t)
      = chi r k x * (2 * ((Real.cos (2 * π * ((k * 2 ^ t : ℕ) : ℝ) / r) : ℝ) : ℂ)) := by
    intro t _
    have h1 : chi r k (x + 2 ^ t) = chi r k x * chi r k (2 ^ t) := chi_add r k x (2 ^ t)
    have h2 : chi r k (x - 2 ^ t) = chi r k x * chi r k (-(2 ^ t)) := by
      rw [sub_eq_add_neg]; exact chi_add r k x (-(2 ^ t))
    have h3 := chi_add_chi_neg r k ((2 : ℤ) ^ t)
    have h4 : ((2 * π * ((k : ℝ) * (((2 : ℤ) ^ t : ℤ) : ℝ)) / r : ℝ))
        = (2 * π * ((k * 2 ^ t : ℕ) : ℝ)) / r := by
      push_cast
      ring
    rw [h1, h2, ← mul_add, h3, h4]
  rw [walkStep, lazyEigen, dyadicEigen, Finset.sum_congr rfl hterm]
  simp only [← Finset.mul_sum]
  push_cast
  field_simp
  ring
