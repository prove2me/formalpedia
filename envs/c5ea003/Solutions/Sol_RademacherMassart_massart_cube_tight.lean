-- Prove2me | solution 1 for RademacherMassart.massart_cube_tight
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:08:26.389128+00:00
-- url     : https://prove2.me/submissions/c8a4792e-6f8e-413d-84ed-a2dd2c6839ee

-- Sol generated from Logic/Rademacher/Massart.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Massart
import Theorems.Thm_RademacherMassart_rad_cube
/-
# Massart's finite class lemma

If a hypothesis class restricted to a sample of size `n` consists of `N` vectors, each
of Euclidean length at most `r`, then its empirical Rademacher complexity is at most

  `r * √(2 log N) / n`.

The proof is the classical Chernoff/MGF argument:

* Jensen's inequality moves the expectation inside the exponential;
* a maximum is bounded by a sum, and the moment generating function of a Rademacher
  sum factorises into hyperbolic cosines, `𝔼 exp(λ⟨σ,v⟩) = ∏ cosh(λ vᵢ)`;
* `cosh t ≤ exp(t²/2)` gives the sub-Gaussian bound `exp(λ²r²/2)`;
* optimising over `λ` yields `√(2 log N)`.

Combined with `Massart` for the class of all `±1` patterns, this shows the bound is
tight up to the absolute constant `√(2 log 2) ≈ 1.177`; see `rad_cube` and
`massart_cube_tight` at the end of the file.

This file is self-contained.
-/

open RademacherMassart

open Finset

variable {n : ℕ}




/-! ### Elementary facts about sign patterns -/





/-! ### The two analytic ingredients -/




/-! ### Massart's lemma -/







/-! ### Tightness: the full sign cube -/






open RademacherMassart in
theorem solution(hn : 0 < n) :
    rad ((cube n : Finset (Fin n → ℝ)) : Set (Fin n → ℝ)) = 1 ∧
      Real.sqrt (n : ℝ) * Real.sqrt (2 * Real.log ((2:ℝ) ^ n)) / n
        = Real.sqrt (2 * Real.log 2) ∧
      (1:ℝ) ≤ Real.sqrt (2 * Real.log 2) ∧ Real.sqrt (2 * Real.log 2) < 6 / 5 := by
  have hn' : (0:ℝ) < n := by exact_mod_cast hn
  refine ⟨rad_cube hn, ?_, ?_, ?_⟩
  · rw [Real.log_pow]
    have : (2:ℝ) * ((n:ℝ) * Real.log 2) = (n:ℝ) * (2 * Real.log 2) := by ring
    rw [this, Real.sqrt_mul (by positivity)]
    have hns : Real.sqrt (n:ℝ) * Real.sqrt (n:ℝ) = (n:ℝ) := Real.mul_self_sqrt hn'.le
    field_simp
    nlinarith [hns]
  · rw [show (1:ℝ) = Real.sqrt 1 by simp]
    apply Real.sqrt_le_sqrt
    nlinarith [Real.log_two_gt_d9]
  · have h : Real.sqrt (2 * Real.log 2) < Real.sqrt ((6/5) ^ 2) := by
      apply Real.sqrt_lt_sqrt (by positivity)
      nlinarith [Real.log_two_lt_d9]
    rwa [Real.sqrt_sq (by norm_num)] at h
