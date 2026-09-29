-- Prove2me | solution 1 for CyclicCubic.root_of_residue_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:37:39.729378+00:00
-- url     : https://prove2.me/submissions/5f30ff6b-f40d-433e-9acf-2efdebc93f5f

-- Sol generated from Applications/CyclicCubicTypeChannel/Splitting.lean
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
/-
# The cyclic cubic field `ℚ(ζ₇ + ζ₇⁻¹)` has exactly two splitting types

## Context (FACT round-32 #3, "THE-CYCLIC-CUBIC-IS-FULLY-PINNED", paper 122)

The real subfield `K = ℚ(ζ₇ + ζ₇⁻¹)` of the seventh cyclotomic field is the
cyclic cubic field of conductor `7`.  Its ring of integers is `ℤ[α]` with
`α = ζ₇ + ζ₇⁻¹` a root of

  `f(X) = X³ + X² − 2X − 1`      (discriminant `49`).

By Dedekind's factorisation criterion the splitting type of an unramified
rational prime `p ≠ 7` in `K` is read off from the factorisation of `f mod p`.
This file proves, from scratch and with no number-field machinery, the complete
arithmetic law behind the experiment:

* `CyclicCubic.root_iff` — for a prime `p ≠ 7`, `f` has a root in `ZMod p`
  **iff** `p ≡ ±1 (mod 7)`;
* `CyclicCubic.splits_completely` — one root forces three *distinct* roots
  (the map `x ↦ x² − 2` cycles them), so `f mod p` either splits completely or
  is irreducible: **only two types**;
* `CyclicCubic.irreducible_mod_of_not_pm_one` — the inert case;
* `CyclicCubic.resDeg_congr` — the residue degree is a function of `p mod 7`
  alone: the arithmetic form of **full pinning**;
* `CyclicCubic.irreducible_rat`, `CyclicCubic.minpoly_zeta_add_inv` — `f` is
  irreducible over `ℚ` and is the minimal polynomial of `ζ₇ + ζ₇⁻¹`, so `K`
  really is a cubic field.

The hard direction ("a root forces `p ≡ ±1`") and the hard existence direction
("`p ≡ −1` forces a root") are both proved by transporting the question into
the group `GL₂(𝔽_p)`: the companion matrix of `Y² − xY + 1` has order `7`
exactly when `x` is a root of `f`, and Cauchy's theorem supplies an order-`7`
matrix in the converse direction, whose trace is then forced to be a root of
`f` by a Cayley–Hamilton recursion.
-/

open Matrix Polynomial

open CyclicCubic

/-! ## The defining cubic -/






/-! ## The `y + y⁻¹` substitution -/

/-- The classical substitution identity `y³·f(y + y⁻¹) = 1 + y + ⋯ + y⁶`. -/
lemma cyclotomic_substitution {K : Type*} [Field K] {y : K} (hy : y ≠ 0) :
    y ^ 3 * fval (y + y⁻¹) = 1 + y + y ^ 2 + y ^ 3 + y ^ 4 + y ^ 5 + y ^ 6 := by
  unfold fval
  field_simp
  ring

/-- A nontrivial seventh root of unity produces a root of `f`. -/
lemma fval_root_of_pow_seven {K : Type*} [Field K] {y : K} (h7 : y ^ 7 = 1) (hne : y ≠ 1) :
    fval (y + y⁻¹) = 0 := by
  have hy : y ≠ 0 := by rintro rfl; simp at h7
  have hid := cyclotomic_substitution hy
  have hgeom : (y - 1) * (1 + y + y ^ 2 + y ^ 3 + y ^ 4 + y ^ 5 + y ^ 6) = 0 := by
    have h : (y - 1) * (1 + y + y ^ 2 + y ^ 3 + y ^ 4 + y ^ 5 + y ^ 6) = y ^ 7 - 1 := by ring
    rw [h, h7, sub_self]
  have h1 : (1 + y + y ^ 2 + y ^ 3 + y ^ 4 + y ^ 5 + y ^ 6 : K) = 0 :=
    (mul_eq_zero.mp hgeom).resolve_left (fun h => hne (sub_eq_zero.mp h))
  exact (mul_eq_zero.mp (hid.trans h1)).resolve_left (pow_ne_zero 3 hy)

/-! ## Small decidable facts about `ZMod 7` -/






/-! ## `2 × 2` matrix toolkit -/


variable {R : Type*} [CommRing R]







/-! ## The splitting criterion -/


variable (p : ℕ) [hp : Fact p.Prime]







/-! ## One root forces three: only two types -/


variable {R : Type*} [CommRing R] [IsDomain R]






/-! ## Irreducibility: the inert type -/


variable (p : ℕ) [hp : Fact p.Prime]









/-! ## The base field: `f` is the minimal polynomial of `ζ₇ + ζ₇⁻¹` -/









open CyclicCubic in
theorem solution(h1 : (p : ZMod 7) = 1) : ∃ x : ZMod p, fval x = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp2 : 2 ≤ p := hp.out.two_le
  have hdvd : (7 : ℕ) ∣ p - 1 := by
    have hc : ((p - 1 : ℕ) : ZMod 7) = 0 := by
      rw [Nat.cast_sub (by omega), h1]; simp
    exact (ZMod.natCast_eq_zero_iff _ _).mp hc
  have hcard : (7 : ℕ) ∣ Fintype.card (ZMod p)ˣ := by
    rwa [ZMod.card_units_eq_totient, Nat.totient_prime hp.out]
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := (ZMod p)ˣ) 7 hcard
  have hu7 : (u : ZMod p) ^ 7 = 1 := by
    have h : u ^ 7 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
    have := congrArg Units.val h
    simpa using this
  have hune : (u : ZMod p) ≠ 1 := by
    intro h
    have hU1 : u = 1 := Units.ext h
    rw [hU1] at hu
    simp at hu
  exact ⟨(u : ZMod p) + (u : ZMod p)⁻¹, fval_root_of_pow_seven hu7 hune⟩
