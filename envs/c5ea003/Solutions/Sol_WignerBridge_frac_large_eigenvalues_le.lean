-- Prove2me | solution 1 for WignerBridge.frac_large_eigenvalues_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:47:26.123022+00:00
-- url     : https://prove2.me/submissions/9c0e6a37-97c4-48cb-86ad-5217c13deb79

-- Sol generated from Probability/WignerBulkTightness.lean
import Mathlib
import Definitions.Def_Probability_WignerMomentGrowth
import Definitions.Def_Probability_WignerTraceBridge
import Theorems.Thm_WignerBridge_normalizedMoment_eq_sum_eigenvalues
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Tightness of the empirical spectral distribution

`Probability.WignerSpectralEdge` bounds the probability that *some* eigenvalue of
`W/√N` is large.  This file records the complementary — and for the semicircle law
more fundamental — statement about the *bulk*: the empirical spectral distribution
(ESD) of `W/√N` puts almost no mass far from the origin, uniformly in the dimension.

* `WignerBridge.frac_large_eigenvalues_le` is deterministic and holds for an
  arbitrary real symmetric matrix: the fraction of eigenvalues of `A/√N` of modulus
  at least `t` is at most `(2k)`-th normalised moment divided by `t^(2k)` — Markov's
  inequality applied to the ESD itself rather than to the ensemble.

* `RademacherWigner.expect_frac_large_eigenvalues_le` combines this with the uniform
  moment bound `expect_normalizedMoment_two_mul_le` to give, for every `k ≥ 1`,

    `E [ #{ i : |λᵢ|/√N ≥ t } / N ] ≤ (k+1)^(2k) / t^(2k)`,

  a bound independent of `N`.

* `RademacherWigner.esd_tight` is the resulting **tightness** statement: for every
  `ε > 0` there is a threshold `t` such that, in *every* dimension, the expected
  fraction of eigenvalues of `W/√N` outside `[-t, t]` is at most `ε`.  Tightness is
  exactly the compactness hypothesis under which convergence of all moments upgrades
  to weak convergence of the ESD, i.e. it is the missing analytic half of the moment
  method (Conjecture 4 of `FUTURE_DIRECTIONS.md`).
-/

open Matrix BigOperators Finset

open WignerBridge



open RademacherWigner

variable {N : ℕ}





open WignerBridge in
theorem solution{N : ℕ} (hN : 0 < N) {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (k : ℕ) {t : ℝ} (ht : 0 < t) :
    (((univ.filter fun i => t ≤ |hA.eigenvalues i| / Real.sqrt (N : ℝ)).card : ℝ) / (N : ℝ))
      ≤ normalizedMoment A (2 * k) / t ^ (2 * k) := by
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcard : (Fintype.card (Fin N) : ℝ) = (N : ℝ) := by simp
  set S : Finset (Fin N) := univ.filter fun i => t ≤ |hA.eigenvalues i| / Real.sqrt (N : ℝ)
    with hS
  set mu : Fin N → ℝ := fun i => hA.eigenvalues i / Real.sqrt (N : ℝ) with hmu
  have hnonneg : ∀ i : Fin N, 0 ≤ (mu i) ^ (2 * k) := by
    intro i
    rw [pow_mul]
    positivity
  have hbig : ∀ i ∈ S, t ^ (2 * k) ≤ (mu i) ^ (2 * k) := by
    intro i hi
    have hti : t ≤ |mu i| := by
      have := (Finset.mem_filter.1 hi).2
      rwa [hmu, abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 : t ^ (2 * k) ≤ |mu i| ^ (2 * k) := pow_le_pow_left₀ ht.le hti _
    rwa [pow_mul, pow_mul, sq_abs, ← pow_mul, ← pow_mul] at h1
  have hsum : (S.card : ℝ) * t ^ (2 * k) ≤ ∑ i : Fin N, (mu i) ^ (2 * k) := by
    calc (S.card : ℝ) * t ^ (2 * k) = ∑ _i ∈ S, t ^ (2 * k) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ S, (mu i) ^ (2 * k) := Finset.sum_le_sum hbig
      _ ≤ ∑ i : Fin N, (mu i) ^ (2 * k) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
            fun i _ _ => hnonneg i
  have hmoment : normalizedMoment A (2 * k) = (1 / (N : ℝ)) * ∑ i : Fin N, (mu i) ^ (2 * k) := by
    rw [normalizedMoment_eq_sum_eigenvalues hA, hcard]
  rw [hmoment, div_le_div_iff₀ hNR (by positivity)]
  have hpos : (0 : ℝ) < t ^ (2 * k) := by positivity
  calc (S.card : ℝ) * t ^ (2 * k) ≤ ∑ i : Fin N, (mu i) ^ (2 * k) := hsum
    _ = 1 / (N : ℝ) * (∑ i : Fin N, (mu i) ^ (2 * k)) * (N : ℝ) := by
        field_simp
