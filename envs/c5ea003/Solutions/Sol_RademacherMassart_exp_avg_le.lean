-- Prove2me | solution 1 for RademacherMassart.exp_avg_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:01:29.505758+00:00
-- url     : https://prove2.me/submissions/6749b8a6-7188-49fa-aa89-46cc83776360

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
theorem solution(y : (Fin n → Bool) → ℝ) :
    Real.exp ((∑ ε : Fin n → Bool, y ε) / 2 ^ n)
      ≤ (∑ ε : Fin n → Bool, Real.exp (y ε)) / 2 ^ n := by
  have hc : (0:ℝ) < 2 ^ n := by positivity
  have hw : ∀ ε ∈ (Finset.univ : Finset (Fin n → Bool)), (0:ℝ) ≤ 1 / 2 ^ n := by
    intro ε _; positivity
  have hsum : ∑ _ε : Fin n → Bool, (1:ℝ) / 2 ^ n = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    simp
  have key := ConvexOn.map_sum_le (𝕜 := ℝ) (t := (Finset.univ : Finset (Fin n → Bool)))
    (w := fun _ => 1 / (2:ℝ) ^ n) (p := y) convexOn_exp hw hsum (fun ε _ => Set.mem_univ _)
  simp only [smul_eq_mul] at key
  calc Real.exp ((∑ ε : Fin n → Bool, y ε) / 2 ^ n)
      = Real.exp (∑ ε : Fin n → Bool, (1 / (2:ℝ) ^ n) * y ε) := by
        rw [← Finset.mul_sum]; ring_nf
    _ ≤ ∑ ε : Fin n → Bool, (1 / (2:ℝ) ^ n) * Real.exp (y ε) := key
    _ = (∑ ε : Fin n → Bool, Real.exp (y ε)) / 2 ^ n := by
        rw [← Finset.mul_sum]; ring
