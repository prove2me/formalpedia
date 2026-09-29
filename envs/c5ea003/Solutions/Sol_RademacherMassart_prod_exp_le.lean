-- Prove2me | solution 1 for RademacherMassart.prod_exp_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:01:30.168648+00:00
-- url     : https://prove2.me/submissions/22115a06-7709-4acf-8aa1-ebf6890b01e8

-- Sol generated from Logic/Rademacher/Massart.lean
import Mathlib
import Definitions.Def_Logic_Rademacher_Massart
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
theorem solution(v : Fin n → ℝ) (l : ℝ) :
    ∏ i, (Real.exp (l * v i) + Real.exp (-(l * v i)))
      ≤ 2 ^ n * Real.exp (l ^ 2 * (∑ i, (v i) ^ 2) / 2) := by
  have hstep : ∀ i : Fin n, Real.exp (l * v i) + Real.exp (-(l * v i))
      ≤ 2 * Real.exp ((l * v i) ^ 2 / 2) := by
    intro i
    have h := Real.cosh_le_exp_half_sq (l * v i)
    rw [Real.cosh_eq] at h
    linarith
  have hnn : ∀ i : Fin n, (0:ℝ) ≤ Real.exp (l * v i) + Real.exp (-(l * v i)) := by
    intro i; positivity
  calc ∏ i, (Real.exp (l * v i) + Real.exp (-(l * v i)))
      ≤ ∏ i, (2 * Real.exp ((l * v i) ^ 2 / 2)) :=
        Finset.prod_le_prod (fun i _ => hnn i) (fun i _ => hstep i)
    _ = 2 ^ n * ∏ i, Real.exp ((l * v i) ^ 2 / 2) := by
        rw [Finset.prod_mul_distrib]; simp
    _ = 2 ^ n * Real.exp (∑ i, (l * v i) ^ 2 / 2) := by rw [Real.exp_sum]
    _ = 2 ^ n * Real.exp (l ^ 2 * (∑ i, (v i) ^ 2) / 2) := by
        congr 2
        rw [Finset.mul_sum, Finset.sum_div]
        exact Finset.sum_congr rfl fun i _ => by ring
