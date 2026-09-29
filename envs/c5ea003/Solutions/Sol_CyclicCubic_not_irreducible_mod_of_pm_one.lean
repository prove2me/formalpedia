-- Prove2me | solution 1 for CyclicCubic.not_irreducible_mod_of_pm_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:39:53.982973+00:00
-- url     : https://prove2.me/submissions/fcd98b74-6600-4f8f-aeb6-4c36e56a8294

-- Sol generated from Applications/CyclicCubicTypeChannel/Splitting.lean
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
import Theorems.Thm_CyclicCubic_residue_of_root
import Theorems.Thm_CyclicCubic_root_of_residue_neg_one
import Theorems.Thm_CyclicCubic_root_of_residue_one
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



@[simp] lemma eval_fpoly {R : Type*} [CommRing R] (x : R) : (fpoly R).eval x = fval x := by
  simp [fpoly, fval]

lemma fpoly_monic (R : Type*) [CommRing R] [Nontrivial R] : (fpoly R).Monic := by
  unfold fpoly; monicity!

lemma fpoly_natDegree (R : Type*) [CommRing R] [Nontrivial R] : (fpoly R).natDegree = 3 := by
  unfold fpoly; compute_degree!

/-! ## The `y + y⁻¹` substitution -/



/-! ## Small decidable facts about `ZMod 7` -/


private lemma cast_seven_zmod7 : ((7 : ℕ) : ZMod 7) = 0 := by decide




/-! ## `2 × 2` matrix toolkit -/


variable {R : Type*} [CommRing R]







/-! ## The splitting criterion -/


variable (p : ℕ) [hp : Fact p.Prime]





/-- **The splitting criterion.**  For a prime `p ≠ 7`, the cubic `f` has a root
modulo `p` exactly when `p ≡ ±1 (mod 7)`, i.e. exactly when the Frobenius of
`p` is trivial in `Gal(K/ℚ) ≅ (ℤ/7)ˣ/{±1}`. -/
theorem root_iff (hp7 : p ≠ 7) :
    (∃ x : ZMod p, fval x = 0) ↔ ((p : ZMod 7) = 1 ∨ (p : ZMod 7) = 6) := by
  refine ⟨residue_of_root p hp7, fun h => ?_⟩
  rcases h with h | h
  · exact root_of_residue_one p h
  · exact root_of_residue_neg_one p h


/-! ## One root forces three: only two types -/


variable {R : Type*} [CommRing R] [IsDomain R]






/-! ## Irreducibility: the inert type -/


variable (p : ℕ) [hp : Fact p.Prime]









/-! ## The base field: `f` is the minimal polynomial of `ζ₇ + ζ₇⁻¹` -/









open CyclicCubic in
theorem solution(hpm : (p : ZMod 7) = 1 ∨ (p : ZMod 7) = 6) :
    ¬ Irreducible (fpoly (ZMod p)) := by
  have hp7 : p ≠ 7 := by
    rintro rfl
    rw [cast_seven_zmod7] at hpm
    rcases hpm with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
  obtain ⟨x, hx⟩ := (root_iff p hp7).mpr hpm
  intro hirr
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three
      (by rw [fpoly_natDegree]; norm_num) (by rw [fpoly_natDegree])] at hirr
  have hmem : x ∈ (fpoly (ZMod p)).roots := by
    rw [Polynomial.mem_roots']
    exact ⟨(fpoly_monic (ZMod p)).ne_zero, by simpa using hx⟩
  rw [hirr] at hmem
  simp at hmem
