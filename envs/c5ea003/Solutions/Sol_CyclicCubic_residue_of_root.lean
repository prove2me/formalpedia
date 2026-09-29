-- Prove2me | solution 1 for CyclicCubic.residue_of_root
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:37:38.573717+00:00
-- url     : https://prove2.me/submissions/e67824fa-28bf-477e-af89-48a55093f957

-- Sol generated from Applications/CyclicCubicTypeChannel/Splitting.lean
import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting
import Theorems.Thm_CyclicCubic_companion_sq
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





private lemma sq_eq_one_zmod7 : ∀ a : ZMod 7, a ^ 2 = 1 → a = 1 ∨ a = 6 := by decide

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



/-- If `x` is a root of `f`, the companion matrix of `Y² − xY + 1` has order dividing `7`. -/
lemma companion_pow_seven {x : R} (hx : fval x = 0) :
    (!![x, -1; 1, 0] : Matrix (Fin 2) (Fin 2) R) ^ 7 = 1 := by
  rw [pow_seven (companion_sq x)]
  have ha : x ^ 6 - 5 * x ^ 4 + 6 * x ^ 2 - 1 = 0 := by
    unfold fval at hx; linear_combination (x ^ 3 - x ^ 2 - 2 * x + 1) * hx
  have hb : x ^ 5 - 4 * x ^ 3 + 3 * x = -1 := by
    unfold fval at hx; linear_combination (x ^ 2 - x - 1) * hx
  rw [ha, hb]
  simp


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
theorem solution(hp7 : p ≠ 7) (h : ∃ x : ZMod p, fval x = 0) :
    (p : ZMod 7) = 1 ∨ (p : ZMod 7) = 6 := by
  obtain ⟨x, hx⟩ := h
  have hp2 : 2 ≤ p := hp.out.two_le
  set M : Matrix (Fin 2) (Fin 2) (ZMod p) := !![x, -1; 1, 0] with hMdef
  have hM7 : M ^ 7 = 1 := companion_pow_seven hx
  have hMne : M ≠ 1 := by
    intro hcon
    have h10 : M 1 0 = (1 : Matrix (Fin 2) (Fin 2) (ZMod p)) 1 0 := by rw [hcon]
    simp [hMdef] at h10
  let U : (Matrix (Fin 2) (Fin 2) (ZMod p))ˣ :=
    ⟨M, M ^ 6, by rw [← pow_succ']; exact hM7, by rw [← pow_succ]; exact hM7⟩
  have hU7 : U ^ 7 = 1 := Units.ext (by simpa using hM7)
  have hUne : U ≠ 1 := fun hcon => hMne (congrArg Units.val hcon)
  have hord : orderOf U = 7 := by
    rcases (Nat.Prime.eq_one_or_self_of_dvd (by norm_num) _
      (orderOf_dvd_of_pow_eq_one hU7)) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hUne
    · exact h
  have hdvd : (7 : ℕ) ∣ (p ^ 2 - 1) * (p ^ 2 - p) := by
    have hdc := orderOf_dvd_natCard (G := GL (Fin 2) (ZMod p)) U
    rwa [hord, Nat.card_eq_fintype_card, card_GL_two p] at hdc
  have hsq : ((p : ZMod 7)) ^ 2 = 1 := by
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp hdvd with h1 | h2
    · have h1' : ((p ^ 2 - 1 : ℕ) : ZMod 7) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h1
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by omega))] at h1'
      push_cast at h1'
      linear_combination h1'
    · have hfac : (p : ℕ) ^ 2 - p = p * (p - 1) := by rw [Nat.mul_sub, mul_one, sq]
      rw [hfac] at h2
      rcases (Nat.Prime.dvd_mul (by norm_num)).mp h2 with hA | hB
      · exact absurd ((Nat.prime_dvd_prime_iff_eq (by norm_num) hp.out).mp hA).symm hp7
      · have hB' : ((p - 1 : ℕ) : ZMod 7) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hB
        rw [Nat.cast_sub (by omega)] at hB'
        push_cast at hB'
        have hone : (p : ZMod 7) = 1 := by linear_combination hB'
        rw [hone]; ring
  exact sq_eq_one_zmod7 _ hsq
