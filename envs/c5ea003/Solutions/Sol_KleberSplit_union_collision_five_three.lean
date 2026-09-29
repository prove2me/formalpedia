-- Prove2me | solution 1 for KleberSplit.union_collision_five_three
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T15:07:59.771277+00:00
-- url     : https://prove2.me/submissions/27ab2d27-f962-41c0-a90e-f33cdefedc39

-- Sol generated from Algebra/KleberComplementaryProducts.lean
import Mathlib
import Definitions.Def_Algebra_KleberComplementaryProducts
import Theorems.Thm_KleberSplit_parts_add_of_disjoint
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
theorem solution:
    ∃ a₁ b₁ a₂ b₂ : Exp 2,
      a₁ + b₁ = a₂ + b₂ ∧
      parts a₁ + parts b₁ = parts a₂ + parts b₂ ∧
      a₁ ≠ a₂ ∧ a₁ ≠ b₂ := by
  classical
  set z : Fin 2 := 0 with hz
  set o : Fin 2 := 1 with ho
  have hzo : z ≠ o := by decide
  refine ⟨Finsupp.single z 3 + Finsupp.single o 1, Finsupp.single z 2 + Finsupp.single o 2,
    Finsupp.single z 3 + Finsupp.single o 2, Finsupp.single z 2 + Finsupp.single o 1,
    ?_, ?_, ?_, ?_⟩
  · rw [show (Finsupp.single z 3 + Finsupp.single o 1 + (Finsupp.single z 2 + Finsupp.single o 2))
        = (Finsupp.single z 3 + Finsupp.single z 2) + (Finsupp.single o 1 + Finsupp.single o 2)
        from by abel,
      show (Finsupp.single z 3 + Finsupp.single o 2 + (Finsupp.single z 2 + Finsupp.single o 1))
        = (Finsupp.single z 3 + Finsupp.single z 2) + (Finsupp.single o 2 + Finsupp.single o 1)
        from by abel]
    rw [add_comm (Finsupp.single o 2) (Finsupp.single o 1)]
  · have hd : ∀ x y : ℕ, x ≠ 0 → y ≠ 0 →
        parts (Finsupp.single z x + Finsupp.single o y) = {x, y} := by
      intro x y hx hy
      have hdisj : Disjoint (Finsupp.single z x).support (Finsupp.single o y).support := by
        rw [Finsupp.support_single_ne_zero z hx, Finsupp.support_single_ne_zero o hy]
        simpa using hzo
      rw [parts_add_of_disjoint hdisj, parts_single, parts_single, if_neg hx, if_neg hy]
      rfl
    rw [hd 3 1 (by norm_num) (by norm_num), hd 2 2 (by norm_num) (by norm_num),
      hd 3 2 (by norm_num) (by norm_num), hd 2 1 (by norm_num) (by norm_num)]
    decide
  · intro h
    have := congrArg (fun d : Exp 2 => d o) h
    simp [hz, ho] at this
  · intro h
    have := congrArg (fun d : Exp 2 => d z) h
    simp [hz, ho] at this
