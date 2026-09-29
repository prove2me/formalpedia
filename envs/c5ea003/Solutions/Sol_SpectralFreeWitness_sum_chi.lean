-- Prove2me | solution 1 for SpectralFreeWitness.sum_chi
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:13:26.486823+00:00
-- url     : https://prove2.me/submissions/6f9cff19-c33c-4b23-b3c2-f709a89e4ba7

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
theorem solution(r : ℕ) (hr : 0 < r) (x : ℤ) :
    ∑ k ∈ range r, chi r k x = r * deltaPer r x := by
  have hr0 : (r : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  set ω : ℂ := Complex.exp (2 * π * Complex.I * (x : ℂ) / r) with hω
  have hchi : ∀ k ∈ range r, chi r k x = ω ^ k := by
    intro k _
    rw [hω, ← Complex.exp_nat_mul, chi]
    congr 1
    ring
  rw [Finset.sum_congr rfl hchi]
  by_cases hdvd : (r : ℤ) ∣ x
  · obtain ⟨m, hm⟩ := id hdvd
    have hω1 : ω = 1 := by
      rw [hω, hm]
      rw [show (2 * (π : ℂ) * Complex.I * ((((r : ℤ) * m : ℤ)) : ℂ) / r)
            = (m : ℂ) * (2 * π * Complex.I) by push_cast; field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I m
    have hd1 : deltaPer r x = 1 := by simp [deltaPer, hdvd]
    rw [hd1, hω1]
    simp
  · have hωr : ω ^ r = 1 := by
      rw [hω, ← Complex.exp_nat_mul]
      rw [show ((r : ℂ) * (2 * π * Complex.I * (x : ℂ) / r)) = (x : ℂ) * (2 * π * Complex.I) by
        field_simp]
      exact Complex.exp_int_mul_two_pi_mul_I x
    have hωne : ω ≠ 1 := by
      intro h
      rw [hω, Complex.exp_eq_one_iff] at h
      obtain ⟨m, hm⟩ := h
      apply hdvd
      refine ⟨m, ?_⟩
      have hπ : ((π : ℂ)) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        exact ne_of_gt Real.pi_pos
      have h2πI : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
        simp [hπ, Complex.I_ne_zero]
      rw [div_eq_iff hr0] at hm
      have hx : (x : ℂ) = (r : ℂ) * (m : ℂ) := by
        apply mul_left_cancel₀ h2πI
        linear_combination hm
      exact_mod_cast hx
    have hgeom : ∑ k ∈ range r, ω ^ k = (ω ^ r - 1) / (ω - 1) :=
      geom_sum_eq hωne r
    rw [hgeom, hωr]
    simp [deltaPer, hdvd]
