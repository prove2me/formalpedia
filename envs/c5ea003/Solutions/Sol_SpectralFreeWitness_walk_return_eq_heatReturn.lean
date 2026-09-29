-- Prove2me | solution 1 for SpectralFreeWitness.walk_return_eq_heatReturn
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:15:53.34984+00:00
-- url     : https://prove2.me/submissions/163e2c4c-dc09-45f5-abfa-17fed51f90be

-- Sol generated from Speculative/AutoResearch/SpectralFreeWitnessWalk.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitnessWalk
import Theorems.Thm_SpectralFreeWitness_sum_chi
import Theorems.Thm_SpectralFreeWitness_walkStep_chi
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



lemma chi_zero_arg (r k : ℕ) : chi r k 0 = 1 := by
  simp [chi]


/-! ## 2. The diffusion operator -/


lemma walkStep_smul (M : ℕ) (c : ℂ) (f : ℤ → ℂ) :
    walkStep M (fun x => c * f x) = fun x => c * walkStep M f x := by
  funext x
  have hterm : ∀ t : ℕ, c * f (x + 2 ^ t) + c * f (x - 2 ^ t)
      = c * (f (x + 2 ^ t) + f (x - 2 ^ t)) := fun t => by ring
  simp only [walkStep, hterm, ← Finset.mul_sum]
  ring

lemma walkStep_sum (M : ℕ) (s : Finset ℕ) (F : ℕ → ℤ → ℂ) :
    walkStep M (fun x => ∑ k ∈ s, F k x) = fun x => ∑ k ∈ s, walkStep M (F k) x := by
  funext x
  simp only [walkStep]
  have e1 : ∑ k ∈ s, (F k x / 2
        + (∑ t ∈ range (M + 1), (F k (x + 2 ^ t) + F k (x - 2 ^ t))) / (4 * ((M : ℂ) + 1)))
      = (∑ k ∈ s, F k x / 2)
        + ∑ k ∈ s, (∑ t ∈ range (M + 1), (F k (x + 2 ^ t) + F k (x - 2 ^ t)))
            / (4 * ((M : ℂ) + 1)) := Finset.sum_add_distrib
  rw [e1, ← Finset.sum_div, ← Finset.sum_div, Finset.sum_comm]
  congr 2
  exact Finset.sum_congr rfl fun t _ => (Finset.sum_add_distrib).symm


lemma walkStep_iterate_smul (M n : ℕ) (c : ℂ) (f : ℤ → ℂ) :
    (walkStep M)^[n] (fun x => c * f x) = fun x => c * ((walkStep M)^[n] f) x := by
  induction n with
  | zero => simp
  | succ m ih =>
      have h1 : (walkStep M)^[m + 1] (fun x => c * f x)
          = walkStep M ((walkStep M)^[m] (fun x => c * f x)) :=
        Function.iterate_succ_apply' _ _ _
      have h2 : (walkStep M)^[m + 1] f = walkStep M ((walkStep M)^[m] f) :=
        Function.iterate_succ_apply' _ _ _
      rw [h1, h2, ih, walkStep_smul]

lemma walkStep_iterate_sum (M n : ℕ) (s : Finset ℕ) (F : ℕ → ℤ → ℂ) :
    (walkStep M)^[n] (fun x => ∑ k ∈ s, F k x)
      = fun x => ∑ k ∈ s, ((walkStep M)^[n] (F k)) x := by
  induction n with
  | zero => simp
  | succ m ih =>
      have h1 : (walkStep M)^[m + 1] (fun x => ∑ k ∈ s, F k x)
          = walkStep M ((walkStep M)^[m] (fun x => ∑ k ∈ s, F k x)) :=
        Function.iterate_succ_apply' _ _ _
      rw [h1, ih, walkStep_sum]
      funext x
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Function.iterate_succ_apply']

lemma walkStep_iterate_chi (r M k n : ℕ) :
    (walkStep M)^[n] (chi r k) = fun x => ((lazyEigen r M k : ℝ) : ℂ) ^ n * chi r k x := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Function.iterate_succ_apply', ih, walkStep_smul, walkStep_chi]
      funext x
      ring

/-! ## 3. Fourier expansion of the delta function -/



/-! ## 4. The return probability equals the spectral heat kernel -/




open SpectralFreeWitness in
theorem solution(r M n : ℕ) (hr : 0 < r) :
    (walkStep M)^[n] (deltaPer r) 0 = ((heatReturn r M n : ℝ) : ℂ) := by
  have hr0 : (r : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    omega
  have hdelta : deltaPer r = fun x => ∑ k ∈ range r, ((r : ℂ)⁻¹ * chi r k x) := by
    funext x
    rw [← Finset.mul_sum, sum_chi r hr x, ← mul_assoc, inv_mul_cancel₀ hr0, one_mul]
  rw [hdelta]
  rw [show (fun x : ℤ => ∑ k ∈ range r, ((r : ℂ)⁻¹ * chi r k x))
      = (fun x : ℤ => ∑ k ∈ range r, (fun y : ℤ => (r : ℂ)⁻¹ * chi r k y) x) from rfl]
  rw [walkStep_iterate_sum]
  show ∑ k ∈ range r, ((walkStep M)^[n] (fun y : ℤ => (r : ℂ)⁻¹ * chi r k y)) 0
      = ((heatReturn r M n : ℝ) : ℂ)
  have hk : ∀ k ∈ range r,
      ((walkStep M)^[n] (fun y : ℤ => (r : ℂ)⁻¹ * chi r k y)) 0
        = (r : ℂ)⁻¹ * ((lazyEigen r M k : ℝ) : ℂ) ^ n := by
    intro k _
    rw [walkStep_iterate_smul, walkStep_iterate_chi]
    simp [chi_zero_arg]
  rw [Finset.sum_congr rfl hk, ← Finset.mul_sum]
  rw [heatReturn]
  push_cast
  ring
