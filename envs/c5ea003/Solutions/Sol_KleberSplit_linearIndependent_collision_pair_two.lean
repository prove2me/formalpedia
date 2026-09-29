-- Prove2me | solution 1 for KleberSplit.linearIndependent_collision_pair_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T14:35:39.522677+00:00
-- url     : https://prove2.me/submissions/dd17b49c-21ec-4cb7-90fb-6eb96b78bcb0

-- Sol generated from Algebra/KleberComplementaryProducts.lean
import Mathlib
import Definitions.Def_Algebra_KleberComplementaryProducts
import Theorems.Thm_KleberSplit_coeff_msym
import Theorems.Thm_KleberSplit_msym_zero
import Theorems.Thm_KleberSplit_parts_add_of_disjoint
import Theorems.Thm_KleberSplit_parts_of_mem_orbit
import Theorems.Thm_KleberSplit_parts_single
/-
# Complementary products of monomial symmetric functions

This file develops, from scratch inside `MvPolynomial (Fin N) R`, the theory needed to
attack the *componentwise splitting independence* phenomenon studied in the paper
"Kleber's conjecture and complementary products of symmetric functions":

> for a partition `θ`, the products `s_α s_β` are linearly independent as `{α, β}` ranges
> over unordered pairs of partitions with `α + β = θ`,

together with its stated analogue for **monomial** symmetric functions over fields of
characteristic zero and over `ℤ`.

Mathlib has no ring of symmetric functions and no Schur functions, so everything here is
built by hand.  We work with *monomial symmetric polynomials* `msym R d`, the sum of all
distinct permutations of a monomial `x^d` in `N` variables; these are exactly the monomial
symmetric functions `m_λ` when `N` is at least the number of parts involved.

## Main results

* `KleberSplit.linearIndependent_msym_mul`: if `{α_i, β_i}` is a finite family of pairs of
  exponent vectors whose *multiset unions* `parts α_i + parts β_i` are pairwise distinct
  (and which fit into `N` variables), then the products `m_{α_i} m_{β_i}` are linearly
  independent over any characteristic-zero domain (in particular over `ℤ` and over any
  field of characteristic zero).
* `KleberSplit.linearIndependent_msym_complementary`: the specialisation to
  componentwise splittings `α_i + β_i = θ` of a fixed `θ`.
* `KleberSplit.linearIndependent_msym`: the monomial symmetric polynomials themselves are
  linearly independent (the case `β = 0`).
* `KleberSplit.linearIndependent_kleber_complementary`: the Kleber-style form, for
  complementary pairs `(λ, ρ - λ)` inside a fixed shape `ρ` (e.g. a rectangle), where the
  hypothesis that the variables suffice is derived rather than assumed.
* `KleberSplit.linearIndependent_row_splittings`: the full one-row case
  `θ = (n)`: the products `m_{(k)} m_{(n-k)}`, `2 * k ≤ n`, are linearly independent.
* `KleberSplit.parts_union_eq_of_msym_mul_eq`: a product `m_α m_β` determines the multiset
  union `parts α + parts β`.
* `KleberSplit.not_linearIndependent_of_too_few_variables` and
  `KleberSplit.linearIndependent_collision_pair_two` (with its special case
  `KleberSplit.linearIndependent_collision_pair`): the two hypotheses are, respectively,
  necessary and not necessary.

The generalisation to products of arbitrarily many factors is in
`Algebra.KleberManyFoldProducts`.

## The mechanism

The Schur-function proof cannot use the dominance-leading term of `s_α s_β`, since every
splitting of `θ` has the *same* leading term `s_θ`.  The mechanism isolated here is the
opposite end of the expansion, controlled by the quadratic statistic
`Qstat d = ∑ i, (d i)^2`:

* `Qstat (u + v) = Qstat u + Qstat v + 2 * dotp u v` (`Qstat_add`), so any monomial
  occurring in `m_α m_β` has `Qstat` **at least** `Qstat α + Qstat β`;
* equality holds exactly when the two exponent vectors have disjoint supports
  (`dotp_eq_zero_iff`), in which case the resulting monomial has part multiset
  `parts α + parts β`, the multiset union.

So the `Qstat`-minimal monomials of `m_α m_β` remember precisely the multiset union of
`α` and `β`, which yields a genuine (non-dominance) triangularity argument.

## Boundary

The hypothesis that the unions are distinct is *not* automatic for componentwise
splittings: `KleberSplit.union_collision_five_three` exhibits two distinct splittings of
`θ = (5,3)` with the same union.  This is exactly the obstruction that makes the full
theorem of the paper hard, and it is recorded here honestly rather than hidden.
-/


open KleberSplit

open Finsupp MvPolynomial Finset

variable {N : ℕ}


/-! ### Parts, orbits and the quadratic statistic -/





lemma self_mem_orbit (d : Exp N) : d ∈ orbit d :=
  Finset.mem_image.2 ⟨Equiv.refl _, Finset.mem_univ _, by simp⟩












/-! ### Monomial symmetric polynomials -/


variable {R : Type*} [CommRing R] {S : Type*} [CommSemiring S]


/-- The coefficients of a product of two monomial symmetric polynomials are the counts of
the ways of splitting the monomial. -/
lemma coeff_msym_mul (a b w : Exp N) :
    MvPolynomial.coeff w (msym S a * msym S b)
      = (((Finset.antidiagonal w).filter
          (fun x : Exp N × Exp N => x.1 ∈ orbit a ∧ x.2 ∈ orbit b)).card : S) := by
  rw [MvPolynomial.coeff_mul, ← Finset.sum_boole]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [coeff_msym, coeff_msym]
  by_cases h1 : x.1 ∈ orbit a <;> by_cases h2 : x.2 ∈ orbit b <;> simp [h1, h2]


/-- Any monomial of the form `u + v` with `u` a rearrangement of `a` and `v` a
rearrangement of `b` really occurs in `m_a * m_b` (over a characteristic-zero ring). -/
lemma coeff_add_mem_orbit_ne_zero [CharZero S] {a b u v : Exp N}
    (hu : u ∈ orbit a) (hv : v ∈ orbit b) :
    MvPolynomial.coeff (u + v) (msym S a * msym S b) ≠ 0 := by
  classical
  set w := u + v with hw
  rw [coeff_msym_mul]
  have hne : (((Finset.antidiagonal w).filter
      (fun x : Exp N × Exp N => x.1 ∈ orbit a ∧ x.2 ∈ orbit b))).Nonempty := by
    refine ⟨(u, v), ?_⟩
    rw [Finset.mem_filter, Finset.mem_antidiagonal]
    exact ⟨rfl, hu, hv⟩
  exact Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 hne)

/-! ### The independence theorem -/










/-! ### The one-row case, unconditionally -/



/-! ### The boundary: unions can collide -/


/-! ### The product determines the multiset union -/


/-! ### Sharpness: enough variables are needed -/




/-! ### Beyond the criterion: the smallest collision class -/





open KleberSplit in
theorem solution[IsDomain R] [CharZero R] {a b : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) :
    LinearIndependent R
      ![msym R (Finsupp.single (0 : Fin (N + 2)) a + Finsupp.single 1 b)
          * msym R (0 : Exp (N + 2)),
        msym R (Finsupp.single (0 : Fin (N + 2)) a)
          * msym R (Finsupp.single (0 : Fin (N + 2)) b)] := by
  classical
  have hdisj : Disjoint (Finsupp.single (0 : Fin (N + 2)) a).support
      (Finsupp.single (1 : Fin (N + 2)) b).support := by
    rw [Finsupp.support_single_ne_zero _ ha, Finsupp.support_single_ne_zero _ hb]
    simp
  have hpartsA :
      parts (Finsupp.single (0 : Fin (N + 2)) a + Finsupp.single 1 b) = {a, b} := by
    rw [parts_add_of_disjoint hdisj, parts_single, parts_single, if_neg ha, if_neg hb]
    rfl
  have hBB : (Finsupp.single (0 : Fin (N + 2)) a) + (Finsupp.single (0 : Fin (N + 2)) b)
      = Finsupp.single (0 : Fin (N + 2)) (a + b) := (Finsupp.single_add _ _ _).symm
  have hpartsBB :
      parts ((Finsupp.single (0 : Fin (N + 2)) a) + (Finsupp.single (0 : Fin (N + 2)) b))
        = {a + b} := by
    rw [hBB, parts_single, if_neg (by omega)]
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [msym_zero, mul_one] at hst
  have h1 : MvPolynomial.coeff
      ((Finsupp.single (0 : Fin (N + 2)) a) + (Finsupp.single (0 : Fin (N + 2)) b))
      (msym R (Finsupp.single (0 : Fin (N + 2)) a + Finsupp.single 1 b)) = 0 := by
    rw [coeff_msym, if_neg]
    intro hmem
    have hp := parts_of_mem_orbit hmem
    rw [hpartsBB, hpartsA] at hp
    have hcard := congrArg Multiset.card hp
    simp at hcard
  have h2 : MvPolynomial.coeff
      ((Finsupp.single (0 : Fin (N + 2)) a) + (Finsupp.single (0 : Fin (N + 2)) b))
      (msym R (Finsupp.single (0 : Fin (N + 2)) a)
        * msym R (Finsupp.single (0 : Fin (N + 2)) b)) ≠ 0 :=
    coeff_add_mem_orbit_ne_zero (self_mem_orbit _) (self_mem_orbit _)
  have hcoeff := congrArg (MvPolynomial.coeff
    ((Finsupp.single (0 : Fin (N + 2)) a) + (Finsupp.single (0 : Fin (N + 2)) b))) hst
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_smul, smul_eq_mul,
    MvPolynomial.coeff_zero, h1, mul_zero, zero_add] at hcoeff
  have ht : t = 0 := by
    rcases mul_eq_zero.1 hcoeff with h | h
    · exact h
    · exact absurd h h2
  subst ht
  refine ⟨?_, rfl⟩
  have hcoeffA := congrArg (MvPolynomial.coeff
    (Finsupp.single (0 : Fin (N + 2)) a + Finsupp.single 1 b)) hst
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, MvPolynomial.coeff_zero, zero_smul,
    add_zero] at hcoeffA
  rw [coeff_msym, if_pos (self_mem_orbit _)] at hcoeffA
  simpa using hcoeffA
