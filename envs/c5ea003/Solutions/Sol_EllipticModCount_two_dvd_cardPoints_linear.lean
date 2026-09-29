-- Prove2me | solution 1 for EllipticModCount.two_dvd_cardPoints_linear
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:17:59.627298+00:00
-- url     : https://prove2.me/submissions/29fb19c3-404b-4b04-85a5-d67e06c0416a

-- Sol generated from Combinatorics/EllipticModP.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticVerticalMoment
import Theorems.Thm_EllipticModCount_two_dvd_cardPoints_iff
/-
# Modular invariants of point counts over the prime fields `ZMod p`

This file specialises the general finite-field results of
`Combinatorics.EllipticPointCount` to the prime fields `F_p = ZMod p`, producing
*exact* point counts and divisibility ("modular") invariants that depend only on
the residue class of `p`.

Main results:

* `EllipticModCount.cardPoints_zmod_eq_of_three` : if `p % 3 = 2` then
  `y^2 = x^3 + b` has exactly `p + 1` points, so `a_p = 0` and `3 ∣ #E(F_p)`.
* `EllipticModCount.cardPoints_zmod_eq_of_four` : if `p % 4 = 3` then
  `y^2 = x^3 + a*x` has exactly `p + 1` points, so `a_p = 0` and `4 ∣ #E(F_p)`.
* `EllipticModCount.two_dvd_cardPoints_zmod_iff` : the 2-torsion parity criterion
  over `F_p`.
* `EllipticModCount.hasse_of_supersingular_three` / `..._four` : the two
  supersingular families satisfy the Hasse bound with equality `a_p = 0`.
-/

open EllipticModCount

open Finset

variable {p : ℕ} [Fact p.Prime]


theorem ringChar_zmod_ne_two (hp : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  exact hp
















/-- **2-torsion parity criterion over `F_p`.** -/
theorem two_dvd_cardPoints_zmod_iff (hp : p ≠ 2) {a b : ZMod p} (hd : disc a b ≠ 0) :
    2 ∣ cardPoints a b ↔ ∃ x : ZMod p, x ^ 3 + a * x + b = 0 :=
  two_dvd_cardPoints_iff (ringChar_zmod_ne_two hp) hd












open EllipticModCount in
theorem solution(hp : p ≠ 2) {a : ZMod p} (ha : a ≠ 0) :
    2 ∣ cardPoints a (0 : ZMod p) := by
  have hd : disc a (0 : ZMod p) ≠ 0 := by
    have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (ringChar_zmod_ne_two hp)
    have h4 : (4 : ZMod p) ≠ 0 := by
      have he : (4 : ZMod p) = 2 * 2 := by norm_num
      rw [he]
      exact mul_ne_zero h2 h2
    simp only [disc, ne_eq]
    intro h
    have : (4 : ZMod p) * a ^ 3 = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · exact h4 h'
    · exact ha (pow_eq_zero_iff (by norm_num) |>.mp h')
  rw [two_dvd_cardPoints_zmod_iff hp hd]
  exact ⟨0, by ring⟩
