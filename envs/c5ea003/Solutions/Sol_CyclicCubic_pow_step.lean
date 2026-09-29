-- Prove2me | solution 1 for CyclicCubic.pow_step
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:48:22.7772+00:00
-- url     : https://prove2.me/submissions/6fcaa030-9f8d-45dc-8fb7-28989395864d

import Mathlib
import Definitions.Def_Applications_CyclicCubicTypeChannel_Splitting

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Applications/CyclicCubicTypeChannel/Splitting.lean ====
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

namespace CyclicCubic

/-! ## The defining cubic -/

-- [dropped: platform already declares fval]
-- [dropped: platform already declares fpoly]
@[simp] lemma eval_fpoly {R : Type*} [CommRing R] (x : R) : (fpoly R).eval x = fval x := by
  simp [fpoly, fval]

lemma fpoly_monic (R : Type*) [CommRing R] [Nontrivial R] : (fpoly R).Monic := by
  unfold fpoly; monicity!

lemma fpoly_natDegree (R : Type*) [CommRing R] [Nontrivial R] : (fpoly R).natDegree = 3 := by
  unfold fpoly; compute_degree!

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

private lemma seven_eq_zero_zmod7 : (7 : ZMod 7) = 0 := by decide

private lemma cast_seven_zmod7 : ((7 : ℕ) : ZMod 7) = 0 := by decide

private lemma one_ne_six_zmod7 : (1 : ZMod 7) ≠ 6 := by decide

private lemma six_sq_sub_one_zmod7 : (6 : ZMod 7) ^ 2 - 1 = 0 := by decide

private lemma sq_eq_one_zmod7 : ∀ a : ZMod 7, a ^ 2 = 1 → a = 1 ∨ a = 6 := by decide

/-! ## `2 × 2` matrix toolkit -/

section Matrices

variable {R : Type*} [CommRing R]

/-- One step of the Chebyshev-type recursion for powers of a determinant-one
`2 × 2` matrix. -/
lemma pow_step {M : Matrix (Fin 2) (Fin 2) R} {t : R} (hM : M ^ 2 = t • M - 1)
    {n : ℕ} {a b : R} (h : M ^ n = a • M - b • 1) :
    M ^ (n + 1) = (a * t - b) • M - a • 1 := by
  rw [pow_succ, h, sub_mul, smul_mul_assoc, smul_mul_assoc, one_mul, ← pow_two, hM,
    smul_sub, smul_smul]
  module

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

/-- Cayley–Hamilton in dimension two. -/
lemma cayley_two [Nontrivial R] (M : Matrix (Fin 2) (Fin 2) R) :
    M ^ 2 = M.trace • M - M.det • 1 := by
  have h := Matrix.aeval_self_charpoly M
  rw [Matrix.charpoly_fin_two] at h
  simp [Polynomial.aeval_def, Polynomial.eval₂_add, Polynomial.eval₂_sub,
    Algebra.algebraMap_eq_smul_one] at h
  linear_combination (norm := module) h

/-- The companion matrix of `Y² − xY + 1` squares as `x·M − 1`. -/
lemma companion_sq (x : R) :
    (!![x, -1; 1, 0] : Matrix (Fin 2) (Fin 2) R) ^ 2 = x • !![x, -1; 1, 0] - 1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

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

end Matrices

/-! ## The splitting criterion -/

section Prime

variable (p : ℕ) [hp : Fact p.Prime]

private lemma card_GL_two : Fintype.card (GL (Fin 2) (ZMod p)) = (p ^ 2 - 1) * (p ^ 2 - p) := by
  rw [← Nat.card_eq_fintype_card, Matrix.card_GL_field]
  simp [Fin.prod_univ_two, ZMod.card]

/-- **Hard direction.**  A root of `f` in `𝔽_p` forces `p ≡ ±1 (mod 7)`. -/
theorem residue_of_root (hp7 : p ≠ 7) (h : ∃ x : ZMod p, fval x = 0) :
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

/-- Existence of a root when `p ≡ 1 (mod 7)`: a seventh root of unity already
lives in `𝔽_p`. -/
theorem root_of_residue_one (h1 : (p : ZMod 7) = 1) : ∃ x : ZMod p, fval x = 0 := by
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

/-- Existence of a root when `p ≡ −1 (mod 7)`.  Here `𝔽_p` contains no seventh
root of unity; instead Cauchy's theorem provides an order-`7` element of
`GL₂(𝔽_p)`, whose trace must be a root of `f`. -/
theorem root_of_residue_neg_one (h6 : (p : ZMod 7) = 6) : ∃ x : ZMod p, fval x = 0 := by
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

/-- **The splitting criterion.**  For a prime `p ≠ 7`, the cubic `f` has a root
modulo `p` exactly when `p ≡ ±1 (mod 7)`, i.e. exactly when the Frobenius of
`p` is trivial in `Gal(K/ℚ) ≅ (ℤ/7)ˣ/{±1}`. -/
theorem root_iff (hp7 : p ≠ 7) :
    (∃ x : ZMod p, fval x = 0) ↔ ((p : ZMod 7) = 1 ∨ (p : ZMod 7) = 6) := by
  refine ⟨residue_of_root p hp7, fun h => ?_⟩
  rcases h with h | h
  · exact root_of_residue_one p h
  · exact root_of_residue_neg_one p h

end Prime

/-! ## One root forces three: only two types -/

section Roots

variable {R : Type*} [CommRing R] [IsDomain R]

omit [IsDomain R] in
/-- The "Frobenius twist" `x ↦ x² − 2` (i.e. `ζ + ζ⁻¹ ↦ ζ² + ζ⁻²`) maps roots of
`f` to roots of `f`. -/
lemma fval_sq_sub_two {x : R} (hx : fval x = 0) : fval (x ^ 2 - 2) = 0 := by
  unfold fval at hx ⊢
  linear_combination (x ^ 3 - x ^ 2 - 2 * x + 1) * hx

/-- A root of `f` is never fixed by the twist, unless `7 = 0`. -/
lemma twist_ne {x : R} (hx : fval x = 0) (h7 : (7 : R) ≠ 0) : x ^ 2 - 2 ≠ x := by
  intro hcon
  have hfix : (x - 2) * (x + 1) = 0 := by linear_combination hcon
  unfold fval at hx
  rcases mul_eq_zero.mp hfix with h | h
  · exact h7 (by linear_combination hx - (x ^ 2 + 3 * x + 4) * h)
  · have h1 : (1 : R) = 0 := by linear_combination hx - (x ^ 2 - 2) * h
    exact one_ne_zero h1

omit [IsDomain R] in
/-- The third root differs from the first, unless `7 = 0`. -/
lemma twist_twist_ne {x : R} (hx : fval x = 0) (h7 : (7 : R) ≠ 0) :
    (x ^ 2 - 2) ^ 2 - 2 ≠ x := by
  intro hcon
  unfold fval at hx
  -- reducing `x⁴ − 4x² + 2 = x` modulo `f` gives `x² + 2x − 1 = 0`, whence `x = 2`
  have hq : x ^ 2 + 2 * x - 1 = 0 := by linear_combination (x - 1) * hx - hcon
  have hx2 : x - 2 = 0 := by linear_combination hx - (x - 1) * hq
  exact h7 (by linear_combination hx - (x ^ 2 + 3 * x + 4) * hx2)

/-- **Splitting is all-or-nothing.**  If `f` has one root in a domain where
`7 ≠ 0`, it has three pairwise distinct roots, permuted cyclically by
`x ↦ x² − 2`.  Together with `root_iff` this is the statement that the cyclic
cubic has only **two** decomposition types: split completely, or inert. -/
theorem splits_completely {x : R} (hx : fval x = 0) (h7 : (7 : R) ≠ 0) :
    fval (x ^ 2 - 2) = 0 ∧ fval ((x ^ 2 - 2) ^ 2 - 2) = 0 ∧
      x ≠ x ^ 2 - 2 ∧ x ^ 2 - 2 ≠ (x ^ 2 - 2) ^ 2 - 2 ∧ x ≠ (x ^ 2 - 2) ^ 2 - 2 := by
  have h2 := fval_sq_sub_two hx
  exact ⟨h2, fval_sq_sub_two h2, fun h => twist_ne hx h7 h.symm,
    fun h => twist_ne h2 h7 h.symm, fun h => twist_twist_ne hx h7 h.symm⟩

end Roots

/-! ## Irreducibility: the inert type -/

section Irred

variable (p : ℕ) [hp : Fact p.Prime]

/-- If `p ≢ ±1 (mod 7)` then `f mod p` is irreducible: `p` is **inert**, with
residue degree `3`. -/
theorem irreducible_mod_of_not_pm_one (hp7 : p ≠ 7)
    (h1 : (p : ZMod 7) ≠ 1) (h6 : (p : ZMod 7) ≠ 6) : Irreducible (fpoly (ZMod p)) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [fpoly_natDegree]; decide
  · intro x hroot
    have hx : fval x = 0 := by simpa using hroot
    rcases residue_of_root p hp7 ⟨x, hx⟩ with h | h
    · exact h1 h
    · exact h6 h

/-- If `p ≡ ±1 (mod 7)` then `f mod p` is *not* irreducible: `p` splits. -/
theorem not_irreducible_mod_of_pm_one (hpm : (p : ZMod 7) = 1 ∨ (p : ZMod 7) = 6) :
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

/-- The **residue degree** of an unramified prime in the cyclic cubic field:
`1` when `p ≡ ±1 (mod 7)` (three primes above `p`), `3` otherwise (inert). -/
-- [dropped: platform already declares resDeg]
theorem resDeg_eq_one_or_three (r : ZMod 7) : resDeg r = 1 ∨ resDeg r = 3 := by
  unfold resDeg; split <;> simp

omit hp in
/-- **Full pinning, arithmetic form.**  The decomposition type of `p` depends on
nothing but `p mod 7`; two primes congruent mod `7` are of the same type. -/
theorem resDeg_congr {q : ℕ} (h : (p : ZMod 7) = (q : ZMod 7)) :
    resDeg (p : ZMod 7) = resDeg (q : ZMod 7) := by rw [h]

/-- The residue degree computes the actual factorisation behaviour: it is `1`
exactly when `f mod p` has a root (equivalently splits completely), and `3`
exactly when `f mod p` is irreducible. -/
theorem resDeg_eq_one_iff (hp7 : p ≠ 7) :
    resDeg (p : ZMod 7) = 1 ↔ ∃ x : ZMod p, fval x = 0 := by
  rw [root_iff p hp7, resDeg]
  by_cases h : (p : ZMod 7) = 1 ∨ (p : ZMod 7) = 6
  · simp [h]
  · rw [if_neg h]
    push_neg at h
    simp [h.1, h.2]

theorem resDeg_eq_three_iff (hp7 : p ≠ 7) :
    resDeg (p : ZMod 7) = 3 ↔ Irreducible (fpoly (ZMod p)) := by
  rw [resDeg]
  by_cases h : (p : ZMod 7) = 1 ∨ (p : ZMod 7) = 6
  · rw [if_pos h]
    exact ⟨fun hcon => absurd hcon (by omega),
      fun hirr => absurd hirr (not_irreducible_mod_of_pm_one p h)⟩
  · rw [if_neg h]
    push_neg at h
    exact ⟨fun _ => irreducible_mod_of_not_pm_one p hp7 h.1 h.2, fun _ => rfl⟩

end Irred

/-! ## The base field: `f` is the minimal polynomial of `ζ₇ + ζ₇⁻¹` -/

section Rational

private lemma map_fpoly_int_zmod2 :
    (fpoly ℤ).map (Int.castRingHom (ZMod 2)) = fpoly (ZMod 2) := by
  simp [fpoly, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul]

private lemma map_fpoly_int_rat : (fpoly ℤ).map (Int.castRingHom ℚ) = fpoly ℚ := by
  simp [fpoly, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul]

/-- `2` is inert (`2 ≢ ±1 mod 7`), so `f mod 2` is irreducible. -/
theorem irreducible_mod_two : Irreducible (fpoly (ZMod 2)) :=
  irreducible_mod_of_not_pm_one 2 (by norm_num) (by decide) (by decide)

/-- `f` is irreducible over `ℚ`; hence `ℚ(ζ₇ + ζ₇⁻¹)` really is a cubic field.
The proof reduces modulo `2`, which is inert by the splitting criterion. -/
theorem irreducible_rat : Irreducible (fpoly ℚ) := by
  have hmonic : (fpoly ℤ).Monic := fpoly_monic ℤ
  have hZ : Irreducible (fpoly ℤ) :=
    hmonic.irreducible_of_irreducible_map (Int.castRingHom (ZMod 2)) _
      (by rw [map_fpoly_int_zmod2]; exact irreducible_mod_two)
  have hQ := (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast
    hmonic.isPrimitive).mp hZ
  rwa [map_fpoly_int_rat] at hQ

/-- `f` is the minimal polynomial of `ζ₇ + ζ₇⁻¹` over `ℚ`: the field studied by
the experiment is the cyclic cubic field of conductor `7`. -/
theorem minpoly_zeta_add_inv {z : ℂ} (h : IsPrimitiveRoot z 7) :
    minpoly ℚ (z + z⁻¹) = fpoly ℚ := by
  have haev : (Polynomial.aeval (z + z⁻¹)) (fpoly ℚ) = fval (z + z⁻¹) := by
    simp [fpoly, fval, Polynomial.aeval_def, Polynomial.eval₂_sub, Polynomial.eval₂_add,
      Polynomial.eval₂_mul, Polynomial.eval₂_pow]
  have hz : (Polynomial.aeval (z + z⁻¹)) (fpoly ℚ) = 0 := by
    rw [haev, fval_root_of_pow_seven h.pow_eq_one (h.ne_one (by norm_num))]
  exact (minpoly.eq_of_irreducible_of_monic irreducible_rat hz (fpoly_monic ℚ)).symm

end Rational

end CyclicCubic
section
open Matrix Polynomial
open CyclicCubic
variable {R : Type*} [CommRing R]

theorem solution {M : Matrix (Fin 2) (Fin 2) R} {t : R} (hM : M ^ 2 = t • M - 1)
    {n : ℕ} {a b : R} (h : M ^ n = a • M - b • 1) :
    M ^ (n + 1) = (a * t - b) • M - a • 1 := by
  first
  | exact CyclicCubic.pow_step hM h
  | exact CyclicCubic.pow_step
  | exact @CyclicCubic.pow_step M t hM n a b h
  | apply CyclicCubic.pow_step
  | exact CyclicCubic.pow_step ..


end
