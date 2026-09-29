-- Prove2me | solution 1 for KleberSplit.linearIndependent_row_splittings
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:07:58.208573+00:00
-- url     : https://prove2.me/submissions/485cd9fb-c08b-4a9a-a7df-459c68b71f43

-- Sol generated from Algebra/KleberComplementaryProducts.lean
import Mathlib
import Definitions.Def_Algebra_KleberComplementaryProducts
import Theorems.Thm_KleberSplit_card_support_single_le
import Theorems.Thm_KleberSplit_linearIndependent_msym_mul
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

















/-! ### Monomial symmetric polynomials -/


variable {R : Type*} [CommRing R] {S : Type*} [CommSemiring S]





/-! ### The independence theorem -/










/-! ### The one-row case, unconditionally -/



/-! ### The boundary: unions can collide -/


/-! ### The product determines the multiset union -/


/-! ### Sharpness: enough variables are needed -/




/-! ### Beyond the criterion: the smallest collision class -/





open KleberSplit in
theorem solution[IsDomain R] [CharZero R] (n : ℕ) :
    LinearIndependent R (fun k : Fin (n / 2 + 1) =>
      msym R (Finsupp.single (0 : Fin (N + 2)) (k : ℕ)) *
        msym R (Finsupp.single (0 : Fin (N + 2)) (n - (k : ℕ)))) := by
  refine linearIndependent_msym_mul _ _ (fun k => ?_) ?_
  · have h1 := card_support_single_le (0 : Fin (N + 2)) (k : ℕ)
    have h2 := card_support_single_le (0 : Fin (N + 2)) (n - (k : ℕ))
    omega
  · intro k l hkl
    have hk : 2 * (k : ℕ) ≤ n := by have := k.2; omega
    have hl : 2 * (l : ℕ) ≤ n := by have := l.2; omega
    simp only [parts_single] at hkl
    refine Fin.ext ?_
    by_cases hk0 : (k : ℕ) = 0
    · by_cases hl0 : (l : ℕ) = 0
      · omega
      · exfalso
        have hnk : n - (k : ℕ) ≠ 0 := by omega
        have hnl : n - (l : ℕ) ≠ 0 := by omega
        rw [if_pos hk0, if_neg hnk, if_neg hl0, if_neg hnl] at hkl
        have hcard := congrArg Multiset.card hkl
        simp at hcard
    · by_cases hl0 : (l : ℕ) = 0
      · exfalso
        have hnk : n - (k : ℕ) ≠ 0 := by omega
        have hnl : n - (l : ℕ) ≠ 0 := by omega
        rw [if_neg hk0, if_neg hnk, if_pos hl0, if_neg hnl] at hkl
        have hcard := congrArg Multiset.card hkl
        simp at hcard
      · have hnk : n - (k : ℕ) ≠ 0 := by omega
        have hnl : n - (l : ℕ) ≠ 0 := by omega
        rw [if_neg hk0, if_neg hnk, if_neg hl0, if_neg hnl] at hkl
        have h1 : (k : ℕ) ∈ ({(l : ℕ)} : Multiset ℕ) + {n - (l : ℕ)} := by
          rw [← hkl]; simp
        have h2 : (l : ℕ) ∈ ({(k : ℕ)} : Multiset ℕ) + {n - (k : ℕ)} := by
          rw [hkl]; simp
        simp at h1 h2
        omega
