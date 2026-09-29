-- Prove2me | solution 1 for RademacherWigner.prob_exists_large_eigenvalue_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-15T03:01:20.815545+00:00
-- url     : https://prove2.me/submissions/997ad8fc-6c5c-498b-affc-815ffc62e578

-- Sol generated from Probability/WignerSpectralEdge.lean
import Mathlib
import Definitions.Def_Probability_WignerMomentGrowth
import Definitions.Def_Probability_WignerRademacherEnsemble
import Definitions.Def_Probability_WignerSpectralEdge
import Theorems.Thm_RademacherWigner_W_isHermitian
import Theorems.Thm_RademacherWigner_card_config_pos
import Theorems.Thm_RademacherWigner_expect_trace_pow_le
import Theorems.Thm_RademacherWigner_markov
import Theorems.Thm_WignerBridge_trace_pow_eq_sum_eigenvalues_real
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# A quantitative spectral-edge bound at every order

`Probability.WignerMomentGrowth` bounds every even trace moment of the symmetric
Rademacher ensemble by `N^(k+1) (k+1)^(2k)`.  Because a single large eigenvalue
already forces a large `2k`-th trace moment, Markov's inequality turns that bound
into a tail estimate for the spectral radius: for every order `k` and every
threshold `t > 0`,

  `P [ some eigenvalue of W/√N has modulus ≥ t ] ≤ N (k+1)^(2k) / t^(2k)`.

This is the classical moment route to the spectral edge; the constant `(k+1)^(2k)`
is the crude spanning-tree count rather than the sharp Catalan constant `4^k`, so
the bound becomes informative for `t` of order `k`, and combined with the
deterministic lower bound `√(1 - 1/N) ≤ ‖W/√N‖` of
`Probability.WignerSemicircleCapstone` it sandwiches the spectral radius from both
sides.
-/

open Matrix BigOperators Finset

open RademacherWigner

variable {N : ℕ}


theorem prob_mono {A B : Finset (Config N)} (h : A ⊆ B) : prob A ≤ prob B := by
  have hM : (0 : ℝ) < (Fintype.card (Config N) : ℝ) := card_config_pos N
  have hcard : (A.card : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast Finset.card_le_card h
  unfold prob
  gcongr


/-- Every even trace moment is nonnegative: it is a sum of even powers of the
eigenvalues. -/
theorem trace_pow_two_mul_nonneg (g : Config N) (k : ℕ) :
    0 ≤ ((W g) ^ (2 * k)).trace := by
  rw [WignerBridge.trace_pow_eq_sum_eigenvalues_real (W_isHermitian g)]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [pow_mul]
  positivity

/-- The expected `2k`-th trace moment, in the form used below. -/
theorem expect_trace_pow_two_mul_le {k : ℕ} (hk : 1 ≤ k) :
    expect (fun g : Config N => ((W g) ^ (2 * k)).trace)
      ≤ (N : ℝ) ^ (k + 1) * ((k : ℝ) + 1) ^ (2 * k) := by
  obtain ⟨m, hm⟩ : ∃ m, m + 1 = 2 * k := ⟨2 * k - 1, by omega⟩
  have h := expect_trace_pow_le (N := N) hm
  rwa [hm] at h



open RademacherWigner in
theorem solution{k : ℕ} (hk : 1 ≤ k) (hN : 0 < N) {t : ℝ}
    (ht : 0 < t) :
    prob (Finset.univ.filter fun g : Config N =>
        ∃ i, t * Real.sqrt (N : ℝ) ≤ |(W_isHermitian g).eigenvalues i|)
      ≤ (N : ℝ) * ((k : ℝ) + 1) ^ (2 * k) / t ^ (2 * k) := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hthr : (0 : ℝ) < t ^ (2 * k) * (N : ℝ) ^ k := by positivity
  -- a large eigenvalue forces a large trace moment
  have hsub : (Finset.univ.filter fun g : Config N =>
        ∃ i, t * Real.sqrt (N : ℝ) ≤ |(W_isHermitian g).eigenvalues i|)
      ⊆ Finset.univ.filter fun g : Config N =>
        t ^ (2 * k) * (N : ℝ) ^ k ≤ ((W g) ^ (2 * k)).trace := by
    intro g hg
    obtain ⟨i, hi⟩ := (Finset.mem_filter.1 hg).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ g, ?_⟩
    have hpow : (t * Real.sqrt (N : ℝ)) ^ (2 * k) = t ^ (2 * k) * (N : ℝ) ^ k := by
      rw [mul_pow, pow_mul (Real.sqrt (N : ℝ)) 2 k, Real.sq_sqrt (le_of_lt hNR)]
    have hle : (t * Real.sqrt (N : ℝ)) ^ (2 * k)
        ≤ ((W_isHermitian g).eigenvalues i) ^ (2 * k) := by
      have h1 : (t * Real.sqrt (N : ℝ)) ^ (2 * k)
          ≤ |(W_isHermitian g).eigenvalues i| ^ (2 * k) :=
        pow_le_pow_left₀ (by positivity) hi (2 * k)
      have h2 : |(W_isHermitian g).eigenvalues i| ^ (2 * k)
          = ((W_isHermitian g).eigenvalues i) ^ (2 * k) := by
        rw [pow_mul, pow_mul, sq_abs]
      rwa [h2] at h1
    have hsum : ((W_isHermitian g).eigenvalues i) ^ (2 * k)
        ≤ ((W g) ^ (2 * k)).trace := by
      rw [WignerBridge.trace_pow_eq_sum_eigenvalues_real (W_isHermitian g)]
      refine Finset.single_le_sum (f := fun i => (W_isHermitian g).eigenvalues i ^ (2 * k))
        (fun j _ => ?_) (Finset.mem_univ i)
      show (0 : ℝ) ≤ (W_isHermitian g).eigenvalues j ^ (2 * k)
      rw [pow_mul]
      positivity
    rw [← hpow]
    exact hle.trans hsum
  refine (prob_mono hsub).trans ?_
  refine (markov (fun g : Config N => ((W g) ^ (2 * k)).trace)
    (fun g => trace_pow_two_mul_nonneg g k) hthr).trans ?_
  rw [div_le_div_iff₀ hthr (by positivity)]
  have hb := expect_trace_pow_two_mul_le (N := N) hk
  have hpos : (0 : ℝ) < t ^ (2 * k) := by positivity
  calc expect (fun g : Config N => ((W g) ^ (2 * k)).trace) * t ^ (2 * k)
      ≤ ((N : ℝ) ^ (k + 1) * ((k : ℝ) + 1) ^ (2 * k)) * t ^ (2 * k) :=
        mul_le_mul_of_nonneg_right hb (le_of_lt hpos)
    _ = (N : ℝ) * ((k : ℝ) + 1) ^ (2 * k) * (t ^ (2 * k) * (N : ℝ) ^ k) := by
        rw [pow_succ]
        ring
