-- Prove2me | solution 1 for RademacherMassart.rad_singleton
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:08:26.931633+00:00
-- url     : https://prove2.me/submissions/4a31093d-a1a1-4de0-b27c-4435be1441f7

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

lemma sum_sign_neg (g : (Fin n → Bool) → ℝ) :
    ∑ ε : Fin n → Bool, g (fun j => !(ε j)) = ∑ ε : Fin n → Bool, g ε := by
  refine Finset.sum_nbij' (fun ε => fun j => !(ε j)) (fun ε => fun j => !(ε j))
    ?_ ?_ ?_ ?_ ?_ <;> intros <;> simp

lemma sgn_neg (ε : Fin n → Bool) (i : Fin n) : sgn (fun j => !(ε j)) i = -sgn ε i := by
  simp only [sgn]
  rcases Bool.eq_false_or_eq_true (ε i) with h | h <;> simp [h]

lemma sum_sgn_eq_zero (i : Fin n) : ∑ ε : Fin n → Bool, sgn ε i = 0 := by
  have h := sum_sign_neg (fun ε => sgn ε i)
  simp only [sgn_neg] at h
  rw [Finset.sum_neg_distrib] at h
  linarith


/-! ### The two analytic ingredients -/




/-! ### Massart's lemma -/







/-! ### Tightness: the full sign cube -/






open RademacherMassart in
theorem solution(v : Fin n → ℝ) : rad ({v} : Set (Fin n → ℝ)) = 0 := by
  unfold rad
  have himg : ∀ ε : Fin n → Bool, sSup (signAvg ε '' ({v} : Set (Fin n → ℝ))) = signAvg ε v := by
    intro ε; simp [Set.image_singleton]
  rw [Finset.sum_congr rfl fun ε _ => himg ε]
  have : ∑ ε : Fin n → Bool, signAvg ε v = 0 := by
    unfold signAvg
    rw [← Finset.mul_sum, Finset.sum_comm]
    have h : ∀ i : Fin n, ∑ ε : Fin n → Bool, sgn ε i * v i = 0 := fun i => by
      rw [← Finset.sum_mul, sum_sgn_eq_zero i, zero_mul]
    simp [h]
  rw [this]; simp
