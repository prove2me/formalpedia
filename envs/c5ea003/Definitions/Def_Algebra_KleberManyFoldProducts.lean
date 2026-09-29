-- Prove2me | Definitions.Def_Algebra_KleberManyFoldProducts
-- name    : Algebra_KleberManyFoldProducts
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:22:16.284642+00:00
-- url     : https://prove2.me/theorems/9d15c453-321f-46d6-b3ef-0b46d21a7bb2
-- title:
--   Aether Catalog definitions — Algebra_KleberManyFoldProducts
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.KleberManyFoldProducts`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/KleberManyFoldProducts.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_KleberComplementaryProducts
/-
# Many-fold complementary products of monomial symmetric functions

A continuation of `Algebra.KleberComplementaryProducts`.  The quadratic-statistic
triangularity used there for products of *two* monomial symmetric functions is not tied to
two factors: here we prove that products `m_{α_1} ⋯ m_{α_r}` of arbitrarily many monomial
symmetric functions are linearly independent as soon as the multiset unions
`parts α_1 + ⋯ + parts α_r` are pairwise distinct.

## Main results

* `KleberSplit.linearIndependent_msym_prod` — many-fold independence.
* `KleberSplit.linearIndependent_psum_monomials` — corollary: linear independence of
  power-sum monomials `p_{k_1} ⋯ p_{k_r}` indexed by multisets of positive exponents.
-/


namespace KleberSplit

open Finsupp MvPolynomial Finset

variable {N : ℕ} {R : Type*} [CommRing R] {S : Type*} [CommSemiring S]

/-! ### Products of arbitrarily many factors

The mechanism above is not restricted to *two* factors.  We now prove the sharper
statement: products `m_{α_1} ⋯ m_{α_r}` of arbitrarily many monomial symmetric functions
are linearly independent as soon as the multiset unions `parts α_1 + ⋯ + parts α_r` are
pairwise distinct.  For `r = 2` this recovers the theorem above.
-/







/-! #### Coefficients of many-fold products -/






/-! ### Application: linear independence of power-sum monomials

Since `m_{(k)} = p_k` is the power sum, a product `∏_j p_{k_j}` is a monomial in the power
sums, and its multiset union is exactly the multiset `{k_j}` of exponents.  The many-fold
theorem therefore recovers the linear independence of the power-sum monomials
`p_{k_1} ⋯ p_{k_r}` indexed by multisets of positive integers, provided there are at least
as many variables as factors.
-/


/-- The power sum `p_k = ∑_j x_j ^ k` in `N` variables. -/
noncomputable def psum (R : Type*) [CommRing R] (N k : ℕ) : MvPolynomial (Fin N) R :=
  ∑ j : Fin N, MvPolynomial.X j ^ k




end KleberSplit


