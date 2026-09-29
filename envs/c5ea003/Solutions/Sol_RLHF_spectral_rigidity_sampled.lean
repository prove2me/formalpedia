-- Prove2me | solution 1 for RLHF.spectral_rigidity_sampled
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:20:30.668053+00:00
-- url     : https://prove2.me/submissions/292139f7-427b-4ff1-b2ec-063569ac79e4

-- Sol generated from NumberTheory/RLHFPronySampling.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFPronySampling
import Definitions.Def_NumberTheory_RLHFSpectralRigidity
import Theorems.Thm_RLHF_exp_sample_uniqueness
import Theorems.Thm_RLHF_rewardMass_eq_zero
import Theorems.Thm_RLHF_sum_exp_eq_rewardMass_sum

/-!
# Finite-sample spectral rigidity: how many temperatures does a reward audit need?

`RLHF.spectral_rigidity` recovers the reward spectrum of an RLHF problem from the value of
the partition function at *every* positive temperature.  This file makes the statement
finite, in both directions, settling the two-atom case of the "Prony count" conjecture
recorded in `FUTURE_DIRECTIONS.md`.

* `RLHF.exp_sample_uniqueness` — **known levels, `n` samples suffice.**  If the candidate
  reward levels `v₀, …, v_{n-1}` are known and distinct, then the masses carried by them are
  determined by the partition function at the `n` arithmetically spaced inverse temperatures
  `t₀, t₀ + τ, …, t₀ + (n−1)τ`.  The engine is a *generalized Vandermonde* determinant: on an
  arithmetic grid of temperatures the exponential-sum system becomes an honest Vandermonde
  system in the variables `e^{v_j τ}`, which are distinct because `exp` is injective.
* `RLHF.spectral_rigidity_sampled` — the RLHF form of the same statement: two RLHF problems
  whose reward values lie in a common known finite list and whose partition functions agree
  at `n` equally spaced inverse temperatures have identical reward spectra.
* `RLHF.prony_three_samples_insufficient` — **unknown levels: three temperatures are not
  enough.**  Two explicit two-atom RLHF problems on `Bool`, with pairwise distinct reward
  levels, whose partition functions agree at the three inverse temperatures `t = 0, 1, 2`,
  and whose reward spectra differ.  The construction is a moment coincidence: the two-point
  distributions `{1, 3}` with masses `(1/2, 1/2)` and `{3/2, 4}` with masses `(4/5, 1/5)`
  have the same mean `2` and the same second moment `5`, and taking logarithms of the
  support turns those two moment equations into agreement of the partition functions at
  `t = 1` and `t = 2` (agreement at `t = 0` being normalization).

Together: the sampling count is governed by whether the reward *levels* are known.  With
known levels `n` measurements are enough; with unknown levels, `2n − 1 = 3` measurements are
provably not enough for `n = 2` atoms.
-/

open RLHF

open Finset

/-! ## 1. Known levels: an arithmetic grid of `n` temperatures suffices -/



/-! ## 2. Unknown levels: three temperatures are not enough -/









open RLHF in
theorem solution{Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    {r₁ p₁ : Ω₁ → ℝ} {r₂ p₂ : Ω₂ → ℝ} {n : ℕ} {v : Fin n → ℝ} (hv : Function.Injective v)
    (h₁ : image r₁ univ ⊆ image v univ) (h₂ : image r₂ univ ⊆ image v univ)
    {t₀ tau : ℝ} (htau : tau ≠ 0)
    (h : ∀ i : Fin n, ∑ y, p₁ y * Real.exp (r₁ y * (t₀ + (i : ℕ) * tau))
      = ∑ y, p₂ y * Real.exp (r₂ y * (t₀ + (i : ℕ) * tau))) :
    ∀ w : ℝ, rewardMass r₁ p₁ w = rewardMass r₂ p₂ w := by
  classical
  have hre₁ : ∀ i : Fin n, ∑ y, p₁ y * Real.exp (r₁ y * (t₀ + (i : ℕ) * tau))
      = ∑ j, rewardMass r₁ p₁ (v j) * Real.exp (v j * (t₀ + (i : ℕ) * tau)) := by
    intro i
    rw [sum_exp_eq_rewardMass_sum h₁ (t₀ + (i : ℕ) * tau),
      Finset.sum_image (fun j _ k _ hjk => hv hjk)]
  have hre₂ : ∀ i : Fin n, ∑ y, p₂ y * Real.exp (r₂ y * (t₀ + (i : ℕ) * tau))
      = ∑ j, rewardMass r₂ p₂ (v j) * Real.exp (v j * (t₀ + (i : ℕ) * tau)) := by
    intro i
    rw [sum_exp_eq_rewardMass_sum h₂ (t₀ + (i : ℕ) * tau),
      Finset.sum_image (fun j _ k _ hjk => hv hjk)]
  have hsample : ∀ i : Fin n,
      ∑ j, rewardMass r₁ p₁ (v j) * Real.exp (v j * (t₀ + (i : ℕ) * tau))
        = ∑ j, rewardMass r₂ p₂ (v j) * Real.exp (v j * (t₀ + (i : ℕ) * tau)) := by
    intro i
    rw [← hre₁ i, ← hre₂ i]
    exact h i
  have hmass := exp_sample_uniqueness hv htau hsample
  intro w
  by_cases hw : w ∈ image v univ
  · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hw
    have := congrFun hmass j
    rwa [hj] at this
  · have hw₁ : w ∉ image r₁ univ := fun hmem => hw (h₁ hmem)
    have hw₂ : w ∉ image r₂ univ := fun hmem => hw (h₂ hmem)
    rw [rewardMass_eq_zero hw₁, rewardMass_eq_zero hw₂]
