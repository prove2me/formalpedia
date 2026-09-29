-- Prove2me | solution 1 for EllipticModCount.quadraticChar_neg_three_zmod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T16:10:57.394558+00:00
-- url     : https://prove2.me/submissions/f579ef9e-c644-4ccc-9a4c-9cf2002478ae

-- Sol generated from Combinatorics/EllipticModP.lean
import Mathlib
import Definitions.Def_Combinatorics_EllipticPointCount
import Definitions.Def_Combinatorics_EllipticVerticalMoment
import Theorems.Thm_EllipticModCount_cube_bijective_iff_char_neg_three
import Theorems.Thm_EllipticModCount_cube_bijective_of_coprime
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

theorem card_zmod_eq : Fintype.card (ZMod p) = p := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact ZMod.card p



/-- For `p % 3 = 2` cubing is a bijection of `F_p`. -/
theorem cube_bijective_zmod (h3 : p % 3 = 2) :
    Function.Bijective fun x : ZMod p => x ^ 3 := by
  apply cube_bijective_of_coprime
  rw [card_zmod_eq]
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hnd : ¬ (3 ∣ (p - 1)) := by omega
  exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hnd |>.symm
















theorem three_ne_zero_zmod (hp3 : p ≠ 3) : (3 : ZMod p) ≠ 0 := by
  intro h
  have hcast : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hcast
  exact hp3 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (by norm_num)).mp hdvd)








open EllipticModCount in
theorem solution(hp2 : p ≠ 2) (hp3 : p ≠ 3) :
    quadraticChar (ZMod p) (-3) = -1 ↔ p % 3 = 2 := by
  have hF := ringChar_zmod_ne_two hp2
  have h3 := three_ne_zero_zmod (p := p) hp3
  rw [← cube_bijective_iff_char_neg_three hF h3]
  constructor
  · intro hbij
    by_contra hmod
    have hprime := (Fact.out : p.Prime)
    have hp0 : p % 3 ≠ 0 := by
      intro h0
      have : (3 : ℕ) ∣ p := Nat.dvd_of_mod_eq_zero h0
      exact hp3 (((Nat.prime_dvd_prime_iff_eq (by norm_num) hprime).mp this).symm)
    have hlt : p % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hmod1 : p % 3 = 1 := by omega
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have hcard : Fintype.card (ZMod p)ˣ = p - 1 := by
      rw [Fintype.card_units, card_zmod_eq]
    have hdvd : 3 ∣ Fintype.card (ZMod p)ˣ := by
      rw [hcard]
      have h2 : 2 ≤ p := hprime.two_le
      omega
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card 3 hdvd
    have hz3 : (z : ZMod p) ^ 3 = 1 := by
      have h1 := pow_orderOf_eq_one z
      rw [hz] at h1
      have h2 := congrArg (Units.val) h1
      push_cast at h2
      exact h2
    have hzne : (z : ZMod p) ≠ 1 := by
      intro h
      have : z = 1 := Units.ext h
      rw [this] at hz
      simp at hz
    exact hzne (hbij.injective (by simpa using hz3))
  · intro hmod
    exact cube_bijective_zmod hmod
