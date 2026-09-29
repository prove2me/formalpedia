-- Prove2me | Theorems.Thm_KleberSplit_coeff_prod_msym_pos
-- name    : KleberSplit.coeff_prod_msym_pos
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:43:08.952744+00:00
-- url     : https://prove2.me/theorems/55ce2828-637e-474d-8de6-7ca8794c0e88
-- title:
--   Every decomposition of a monomial into rearrangements really contributes.
-- statement:
--   Every decomposition of a monomial into rearrangements really contributes.
--
--   ```lean
--   theorem KleberSplit.coeff_prod_msym_pos{κ : Type*} [DecidableEq κ] (s : Finset κ) (f u : κ → Exp N)
--       (hu : ∀ j ∈ s, u j ∈ orbit (f j)) :
--       0 < MvPolynomial.coeff (∑ j ∈ s, u j) (∏ j ∈ s, msym ℕ (f j)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/KleberManyFoldProducts.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/KleberManyFoldProducts.lean#L167

-- Thm stub generated from Algebra/KleberManyFoldProducts.lean
import Mathlib
import Definitions.Def_Algebra_KleberComplementaryProducts
import Definitions.Def_Algebra_KleberManyFoldProducts
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


open KleberSplit

open Finsupp MvPolynomial Finset

variable {N : ℕ} {R : Type*} [CommRing R] {S : Type*} [CommSemiring S]

/-! ### Products of arbitrarily many factors

The mechanism above is not restricted to *two* factors.  We now prove the sharper
statement: products `m_{α_1} ⋯ m_{α_r}` of arbitrarily many monomial symmetric functions
are linearly independent as soon as the multiset unions `parts α_1 + ⋯ + parts α_r` are
pairwise distinct.  For `r = 2` this recovers the theorem above.
-/







/-! #### Coefficients of many-fold products -/

theorem KleberSplit.coeff_prod_msym_pos{κ : Type*} [DecidableEq κ] (s : Finset κ) (f u : κ → Exp N)
    (hu : ∀ j ∈ s, u j ∈ orbit (f j)) :
    0 < MvPolynomial.coeff (∑ j ∈ s, u j) (∏ j ∈ s, msym ℕ (f j)) := by sorry
