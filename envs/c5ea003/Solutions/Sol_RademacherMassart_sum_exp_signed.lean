-- Prove2me | solution 1 for RademacherMassart.sum_exp_signed
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:01:30.836582+00:00
-- url     : https://prove2.me/submissions/28b94e0b-6a5c-432b-ad17-1c769e1af769

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
    ∑ ε : Fin n → Bool, Real.exp (l * ∑ i, sgn ε i * v i)
      = ∏ i, (Real.exp (l * v i) + Real.exp (-(l * v i))) := by
  classical
  have hfac : ∀ ε : Fin n → Bool,
      Real.exp (l * ∑ i, sgn ε i * v i) = ∏ i, Real.exp (l * sgn ε i * v i) := by
    intro ε
    rw [← Real.exp_sum, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have h := Finset.prod_univ_sum (κ := fun _ : Fin n => Bool)
      (fun _ => (Finset.univ : Finset Bool))
      (fun i b => Real.exp (l * (if b then (1:ℝ) else -1) * v i))
  rw [Fintype.piFinset_univ] at h
  rw [Finset.sum_congr rfl (fun ε _ => hfac ε)]
  simp only [sgn]
  rw [← h]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  norm_num
