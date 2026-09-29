-- Prove2me | solution 1 for RLHF.spectral_rigidity_sampled_general
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:20:31.20743+00:00
-- url     : https://prove2.me/submissions/5a3f4fcb-650c-45d2-a702-2c8a435cc4c4

-- Sol generated from NumberTheory/RLHFChebyshevSystem.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFPronySampling
import Definitions.Def_NumberTheory_RLHFSpectralRigidity
import Theorems.Thm_RLHF_exp_sample_uniqueness_general
import Theorems.Thm_RLHF_rewardMass_eq_zero
import Theorems.Thm_RLHF_sum_exp_eq_rewardMass_sum

/-!
# Exponential sums form a Chebyshev system: `n` arbitrary temperatures suffice

`RLHF.exp_sample_uniqueness` recovers the masses on `n` known reward levels from the
partition function at `n` *arithmetically spaced* inverse temperatures, by a Vandermonde
determinant.  This file removes the arithmetic-grid hypothesis: **any** `n` distinct
temperatures do.

The engine is the classical Descartes/Chebyshev fact, proved here by induction on the number
of exponents with Rolle's theorem supplying the inductive step:

* `RLHF.expPoly_eq_zero_of_zeros` — a real exponential polynomial `∑_{j<n} c_j e^{v_j x}`
  with `n` strictly increasing exponents that vanishes at `n` distinct points has all
  coefficients zero.  (Equivalently: a nonzero exponential polynomial with `n` exponents has
  at most `n − 1` real zeros.)
* `RLHF.exp_sample_uniqueness_general` — consequently two mass vectors on the same `n` known
  distinct levels are equal as soon as their exponential sums agree at `n` distinct
  temperatures.
* `RLHF.spectral_rigidity_sampled_general` — the RLHF audit statement: with `n` known
  candidate reward levels, `n` arbitrary distinct inverse temperatures determine the reward
  spectrum.

Combined with `RLHF.prony_three_samples_insufficient_spectra`, the picture for the sampling
question is complete in the known-level case, and provably different when the levels are
unknown.
-/

open RLHF

open Finset






open RLHF in
theorem solution{Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    {r₁ p₁ : Ω₁ → ℝ} {r₂ p₂ : Ω₂ → ℝ} {n : ℕ} {v : Fin n → ℝ} (hv : StrictMono v)
    (h₁ : image r₁ univ ⊆ image v univ) (h₂ : image r₂ univ ⊆ image v univ)
    {t : Fin n → ℝ} (ht : StrictMono t)
    (h : ∀ i, ∑ y, p₁ y * Real.exp (r₁ y * t i) = ∑ y, p₂ y * Real.exp (r₂ y * t i)) :
    ∀ w : ℝ, rewardMass r₁ p₁ w = rewardMass r₂ p₂ w := by
  classical
  have hre₁ : ∀ i, ∑ y, p₁ y * Real.exp (r₁ y * t i)
      = ∑ j, rewardMass r₁ p₁ (v j) * Real.exp (v j * t i) := by
    intro i
    rw [sum_exp_eq_rewardMass_sum h₁ (t i),
      Finset.sum_image (fun j _ k _ hjk => hv.injective hjk)]
  have hre₂ : ∀ i, ∑ y, p₂ y * Real.exp (r₂ y * t i)
      = ∑ j, rewardMass r₂ p₂ (v j) * Real.exp (v j * t i) := by
    intro i
    rw [sum_exp_eq_rewardMass_sum h₂ (t i),
      Finset.sum_image (fun j _ k _ hjk => hv.injective hjk)]
  have hsample : ∀ i, ∑ j, rewardMass r₁ p₁ (v j) * Real.exp (v j * t i)
      = ∑ j, rewardMass r₂ p₂ (v j) * Real.exp (v j * t i) := by
    intro i
    rw [← hre₁ i, ← hre₂ i]
    exact h i
  have hmass := exp_sample_uniqueness_general hv ht hsample
  intro w
  by_cases hw : w ∈ image v univ
  · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hw
    have := congrFun hmass j
    rwa [hj] at this
  · have hw₁ : w ∉ image r₁ univ := fun hmem => hw (h₁ hmem)
    have hw₂ : w ∉ image r₂ univ := fun hmem => hw (h₂ hmem)
    rw [rewardMass_eq_zero hw₁, rewardMass_eq_zero hw₂]
