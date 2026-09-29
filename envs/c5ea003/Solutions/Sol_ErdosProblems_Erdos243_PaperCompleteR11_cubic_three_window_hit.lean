-- Prove2me | solution 1 for ErdosProblems.Erdos243.PaperCompleteR11.cubic_three_window_hit
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-24T23:05:14.311412+00:00
-- url     : https://prove2.me/submissions/08226df2-a13c-475d-acc6-c79cb1755171

import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR9_PolynomialCorrections
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_WindowIncidence
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_isSquare_square_mul_iff
import Theorems.Thm_ErdosProblems_Erdos243_PaperCompleteR11_zero_middle_neighbour_square
import Mathlib
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientRing
import Mathlib.Tactic

/-!
# From actual modular cubic roots to the exceptional-set density

Rational profile coefficients are cleared over the
integers before reduction. There is deliberately no ring homomorphism from
`ℚ` to `ZMod p`. The final theorem is conditional on an actual divergent family
of good primes; producing that family from a number-field nonsquare remains a
separate global obligation, not a premise silently claimed to have been proved.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11
open scoped BigOperators




/-- A cleared cubic root gives the exact negative-neighbour-product identity. -/
theorem cleared_cubic_neighbour_product {K : Type*} [CommRing K]
    (A B r : K) (hroot : A * (r ^ 3 - r) + B = 0) :
    -(A * ((r - 1) ^ 3 - (r - 1)) + B) *
      (A * ((r + 1) ^ 3 - (r + 1)) + B) =
        (3 * A * r) ^ 2 * (r ^ 2 - 1) := by
  have hl : A * ((r - 1) ^ 3 - (r - 1)) + B = -3 * A * r * (r - 1) := by
    linear_combination hroot
  have hr : A * ((r + 1) ^ 3 - (r + 1)) + B = 3 * A * r * (r + 1) := by
    linear_combination hroot
  rw [hl, hr]
  ring
end ErdosProblems.Erdos243.PaperCompleteR11

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.PaperCompleteR11 in
theorem solution {K : Type*} [Field K]
    (u v a : ℕ → K) (A B r : K) (T n : ℕ) (hn : T ≤ n)
    (hnum : ∀ j, T ≤ j → u (j + 1) = a j * u j - v j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j)
    (hroot : A * (r ^ 3 - r) + B = 0)
    (hfactor : 3 * A * r ≠ 0) (hns : ¬ IsSquare (r ^ 2 - 1))
    (hphase : (n : K) = r - 2) :
    ∃ j : ℕ, j < 3 ∧ u (n + j) ≠
      A * ((((n + j : ℕ) : K) + 1) ^ 3 - (((n + j : ℕ) : K) + 1)) + B := by
  by_contra hbad
  have hagree : ∀ j : ℕ, j < 3 → u (n + j) =
      A * ((((n + j : ℕ) : K) + 1) ^ 3 - (((n + j : ℕ) : K) + 1)) + B := by
    intro j hj
    by_contra he
    exact hbad ⟨j, hj, he⟩
  have hu0 : u n = A * ((r - 1) ^ 3 - (r - 1)) + B := by
    have h := hagree 0 (by decide)
    simp only [Nat.add_zero, hphase] at h
    convert h using 1 <;> ring
  have hu1 : u (n + 1) = 0 := by
    have h := hagree 1 (by decide)
    simp only [Nat.cast_add, Nat.cast_one, hphase] at h
    calc
      u (n + 1) = A * (r ^ 3 - r) + B := by convert h using 1 <;> ring
      _ = 0 := hroot
  have hu2 : u (n + 2) = A * ((r + 1) ^ 3 - (r + 1)) + B := by
    have h := hagree 2 (by decide)
    simp only [Nat.cast_add, Nat.cast_ofNat, hphase] at h
    convert h using 1 <;> ring
  have hz : a n * u n - v n = 0 := by rw [← hnum n hn, hu1]
  have hnext : u (n + 2) = -(a n * v n) := by
    have h := hnum (n + 1) (by omega)
    simpa only [Nat.add_assoc, hu1, hden n hn, mul_zero, zero_sub] using h
  have hs := zero_middle_neighbour_square (u n) (u (n + 2)) (a n) (v n) hz hnext
  rw [hu0, hu2, cleared_cubic_neighbour_product A B r hroot] at hs
  exact hns ((isSquare_square_mul_iff (3 * A * r) (r ^ 2 - 1) hfactor).mp hs)
