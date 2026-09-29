-- Prove2me | solution 1 for CollatzSpectralGap.no_uniform_irrational_spectral_gap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T20:44:55.928751+00:00
-- url     : https://prove2.me/submissions/8e5d4531-e74e-4434-aedc-56c03ee3d859

-- Sol generated from MachineLearning/CollatzSpectralGap.lean
import Mathlib
import Definitions.Def_MachineLearning_CollatzSpectralGap

/-!
# A Fourier obstruction to the proposed Collatz spectral gap

For a finite cutoff, the Collatz exponential sum is continuous in frequency and
has value `N` at frequency zero. Since irrational frequencies are dense, its
norm is arbitrarily close to `N` at irrational frequencies. Consequently, no
uniform bound smaller than `N`—in particular no bound smaller than `√N` when
`N > 1`—can hold at every irrational frequency.
-/

open CollatzSpectralGap

open scoped ComplexConjugate
open Filter Set



/-- A continuous complex-valued function taking the value `N` at zero exceeds
any bound `C < N` at some irrational point. This is the topological mechanism
behind the obstruction. -/
theorem irrational_frequency_near_peak
    (f : ℝ → ℂ) (N : ℕ) (C : ℝ) (hf : Continuous f)
    (hzero : f 0 = N) (hC : C < N) :
    ∃ ω : ℝ, Irrational ω ∧ C < ‖f ω‖ := by
  obtain ⟨ε, hε, hball⟩ :
      ∃ ε > 0, ∀ x, abs x < ε → C < ‖f x‖ := by
    rcases Metric.mem_nhds_iff.mp
        (hf.norm.continuousAt.eventually
          (lt_mem_nhds (show C < ‖f 0‖ by simpa [hzero] using hC))) with
      ⟨ε, hε, hball⟩
    exact ⟨ε, hε, by aesop⟩
  obtain ⟨ω, hω, hωpos, hωε⟩ := exists_irrational_btwn hε
  exact ⟨ω, hω, hball ω (by rw [abs_of_pos hωpos]; exact hωε)⟩

/-- The finite Collatz Fourier sum is continuous in its real frequency. -/
theorem continuous_collatzFourier (N : ℕ) :
    Continuous (collatzFourier N) := by
  refine' continuous_finset_sum _ _
  fun_prop







open CollatzSpectralGap in
theorem solution    (N : ℕ) (C : ℝ) (hN : 1 < N) (hC : C < Real.sqrt N) :
    ∃ ω : ℝ, Irrational ω ∧ C < ‖collatzFourier N ω‖ := by
  apply irrational_frequency_near_peak (collatzFourier N) N C
  · exact continuous_collatzFourier N
  · simp [collatzFourier]
  · calc
      C < Real.sqrt N := hC
      _ < N := by
        have hs : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
        have hs2 : (Real.sqrt (N : ℝ)) ^ 2 = N := by
          rw [Real.sq_sqrt]
          positivity
        have hNr : (1 : ℝ) < N := by exact_mod_cast hN
        nlinarith
