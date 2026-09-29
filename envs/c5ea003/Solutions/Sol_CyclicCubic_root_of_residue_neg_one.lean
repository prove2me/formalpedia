-- Prove2me | solution 1 for CyclicCubic.root_of_residue_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:37:39.179697+00:00
-- url     : https://prove2.me/submissions/1ee0a1c3-bb42-471e-b826-649cf2d87e5b

-- Sol generated from Applications/CyclicCubicTypeChannel/Splitting.lean
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
import Theorems.Thm_CyclicCubic_cayley_two
import Theorems.Thm_CyclicCubic_pow_step
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



/-! ## Small decidable facts about `ZMod 7` -/

private lemma seven_eq_zero_zmod7 : (7 : ZMod 7) = 0 := by decide


private lemma one_ne_six_zmod7 : (1 : ZMod 7) ≠ 6 := by decide

private lemma six_sq_sub_one_zmod7 : (6 : ZMod 7) ^ 2 - 1 = 0 := by decide


/-! ## `2 × 2` matrix toolkit -/


variable {R : Type*} [CommRing R]


/-- Seventh power of a determinant-one `2 × 2` matrix, in terms of its trace. -/
lemma pow_seven {M : Matrix (Fin 2) (Fin 2) R} {t : R} (hM : M ^ 2 = t • M - 1) :
    M ^ 7 = (t ^ 6 - 5 * t ^ 4 + 6 * t ^ 2 - 1) • M
      - (t ^ 5 - 4 * t ^ 3 + 3 * t) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  have e2 : M ^ 2 = t • M - (1 : R) • 1 := by simpa using hM
  have e7 := pow_step hM (pow_step hM (pow_step hM (pow_step hM (pow_step hM e2))))
  rw [e7]
  congr 1
  · congr 1; ring
  · congr 1; ring





/-! ## The splitting criterion -/


variable (p : ℕ) [hp : Fact p.Prime]

private lemma card_GL_two : Fintype.card (GL (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]






/-! ## One root forces three: only two types -/


variable {R : Type*} [CommRing R] [IsDomain R]






/-! ## Irreducibility: the inert type -/


variable (p : ℕ) [hp : Fact p.Prime]









/-! ## The base field: `f` is the minimal polynomial of `ζ₇ + ζ₇⁻¹` -/









open CyclicCubic in
theorem solution(h6 : (p : ZMod 7) = 6) : ∃ x : ZMod p, fval x = 0 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hp2 : 2 ≤ p := hp.out.two_le
  have hnd : ¬ (7 ∣ p - 1) := by
    rintro ⟨k, hk⟩
    have hpk : p = 7 * k + 1 := by omega
    rw [hpk] at h6
    push_cast at h6
    rw [seven_eq_zero_zmod7, zero_mul, zero_add] at h6
    exact one_ne_six_zmod7 h6
  have hgcd7 : Nat.gcd 7 (p - 1) = 1 := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hnd
  have hdvdcard : (7 : ℕ) ∣ Fintype.card (GL (Fin 2) (ZMod p)) := by
    have h1 : (7 : ℕ) ∣ p ^ 2 - 1 := by
      have hc : ((p ^ 2 - 1 : ℕ) : ZMod 7) = 0 := by
        rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))]
        push_cast
        rw [h6]; exact six_sq_sub_one_zmod7
      exact (ZMod.natCast_eq_zero_iff _ _).mp hc
    rw [card_GL_two p]
    exact Dvd.dvd.mul_right h1 _
  obtain ⟨U, hU⟩ := exists_prime_orderOf_dvd_card (G := GL (Fin 2) (ZMod p)) 7 hdvdcard
  have hU7 : U ^ 7 = 1 := by rw [← hU]; exact pow_orderOf_eq_one U
  set M : Matrix (Fin 2) (Fin 2) (ZMod p) := U.val with hMdef
  have hM7 : M ^ 7 = 1 := by
    have h : (U ^ 7).val = (1 : GL (Fin 2) (ZMod p)).val := by rw [hU7]
    simpa [hMdef] using h
  have hdet : M.det = 1 := by
    have hd7 : M.det ^ 7 = 1 := by rw [← Matrix.det_pow, hM7, Matrix.det_one]
    have hdne : M.det ≠ 0 := by
      intro h0
      rw [h0] at hd7
      simp at hd7
    have hgcd : orderOf M.det ∣ Nat.gcd 7 (p - 1) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hd7)
        (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hdne))
    rw [hgcd7, Nat.dvd_one] at hgcd
    exact orderOf_eq_one_iff.mp hgcd
  set t := M.trace with ht
  have hM2 : M ^ 2 = t • M - 1 := by rw [cayley_two M, hdet, one_smul]
  have hkey := pow_seven hM2
  rw [hM7] at hkey
  set A := t ^ 6 - 5 * t ^ 4 + 6 * t ^ 2 - 1 with hA
  set B := t ^ 5 - 4 * t ^ 3 + 3 * t with hB
  by_cases hA0 : A = 0
  · have hfac : fval t * (t ^ 3 - t ^ 2 - 2 * t + 1) = 0 := by
      unfold fval; rw [hA] at hA0; linear_combination hA0
    rcases mul_eq_zero.mp hfac with h | h
    · exact ⟨t, h⟩
    · exact ⟨-t, by unfold fval; linear_combination -h⟩
  · exfalso
    have hscal : A • M = (1 + B) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
      linear_combination (norm := module) -hkey
    have hMc : M = (A⁻¹ * (1 + B)) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) := by
      have h2 := congrArg (fun N => A⁻¹ • N) hscal
      simpa [smul_smul, inv_mul_cancel₀ hA0] using h2
    set c := A⁻¹ * (1 + B) with hc
    have hc7 : c ^ 7 = 1 := by
      have h3 : (c • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))) ^ 7 = 1 := by rw [← hMc]; exact hM7
      rw [_root_.smul_pow, one_pow] at h3
      have h10 : (c ^ 7) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) = (1 : ZMod p) • 1 := by
        simpa using h3
      have h11 := congrArg (fun N : Matrix (Fin 2) (Fin 2) (ZMod p) => N 0 0) h10
      simpa [Matrix.one_apply] using h11
    have hcne : c ≠ 0 := by
      intro h0
      rw [h0] at hc7
      simp at hc7
    have hgcd : orderOf c ∣ Nat.gcd 7 (p - 1) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc7)
        (orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hcne))
    rw [hgcd7, Nat.dvd_one] at hgcd
    have hc1 : c = 1 := orderOf_eq_one_iff.mp hgcd
    have hM1 : M = 1 := by rw [hMc, hc1, one_smul]
    have hU1 : U = 1 := Units.ext hM1
    rw [hU1] at hU
    simp at hU
