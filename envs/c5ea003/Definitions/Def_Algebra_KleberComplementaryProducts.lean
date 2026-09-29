-- Prove2me | Definitions.Def_Algebra_KleberComplementaryProducts
-- name    : Algebra_KleberComplementaryProducts
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:21:41.471428+00:00
-- url     : https://prove2.me/theorems/667621aa-f807-4ef0-9d93-c650c78ef568
-- title:
--   Aether Catalog definitions — Algebra_KleberComplementaryProducts
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.KleberComplementaryProducts`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/KleberComplementaryProducts.lean by skeleton subtraction
import Mathlib
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


namespace KleberSplit

open Finsupp MvPolynomial Finset

variable {N : ℕ}

/-- Exponent vectors of monomials in `N` variables. -/
abbrev Exp (N : ℕ) := Fin N →₀ ℕ

/-! ### Parts, orbits and the quadratic statistic -/

/-- The multiset of nonzero parts of an exponent vector, i.e. the partition it rearranges
to (as an unordered multiset). -/
def parts (d : Exp N) : Multiset ℕ := d.support.val.map d

/-- The orbit of an exponent vector under permutations of the `N` variables. -/
def orbit (d : Exp N) : Finset (Exp N) :=
  Finset.univ.image (fun e : Equiv.Perm (Fin N) => Finsupp.equivMapDomain e d)

/-- The quadratic statistic `∑ i, d i ^ 2`; it is permutation invariant and superadditive
with an explicit error term. -/
def Qstat (d : Exp N) : ℕ := ∑ i : Fin N, (d i) ^ 2

/-- The inner product of two exponent vectors. -/
def dotp (u v : Exp N) : ℕ := ∑ i : Fin N, u i * v i













/-! ### Monomial symmetric polynomials -/

/-- The monomial symmetric polynomial attached to an exponent vector: the sum of all
distinct rearrangements of the monomial `x ^ d`. -/
noncomputable def msym (R : Type*) [CommSemiring R] (d : Exp N) : MvPolynomial (Fin N) R :=
  ∑ w ∈ orbit d, MvPolynomial.monomial w (1 : R)

variable {R : Type*} [CommRing R] {S : Type*} [CommSemiring S]





/-! ### The independence theorem -/










/-! ### The one-row case, unconditionally -/



/-! ### The boundary: unions can collide -/


/-! ### The product determines the multiset union -/


/-! ### Sharpness: enough variables are needed -/




/-! ### Beyond the criterion: the smallest collision class -/




end KleberSplit


