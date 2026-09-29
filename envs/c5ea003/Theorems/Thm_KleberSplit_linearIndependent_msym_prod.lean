-- Prove2me | Theorems.Thm_KleberSplit_linearIndependent_msym_prod
-- name    : KleberSplit.linearIndependent_msym_prod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:43:23.827432+00:00
-- url     : https://prove2.me/theorems/a82b8a39-0a26-4a67-86d9-aea0bb37c8bd
-- title:
--   Independence of many-fold products with distinct multiset unions.
-- statement:
--   **Independence of many-fold products with distinct multiset unions.**
--
--   Let `f i j` (`j ∈ s`) be finite families of exponent vectors, one family for each index
--   `i`, each family jointly fitting into `N` variables.  If the multiset unions
--   `∑ j ∈ s, parts (f i j)` are pairwise distinct, then the products
--   `∏ j ∈ s, m_{f i j}` are linearly independent over any characteristic-zero domain.
--
--   For `s` of size two this is `linearIndependent_msym_mul`.
--
--   ```lean
--   theorem KleberSplit.linearIndependent_msym_prod[IsDomain R] [CharZero R]
--       {ι κ : Type*} [Fintype ι] [DecidableEq κ] (s : Finset κ) (f : ι → κ → Exp N)
--       (hcard : ∀ i, ∑ j ∈ s, (f i j).support.card ≤ N)
--       (hinj : Function.Injective fun i => ∑ j ∈ s, parts (f i j)) :
--       LinearIndependent R (fun i => ∏ j ∈ s, msym R (f i j)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/KleberManyFoldProducts.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/KleberManyFoldProducts.lean#L228

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

theorem KleberSplit.linearIndependent_msym_prod[IsDomain R] [CharZero R]
    {ι κ : Type*} [Fintype ι] [DecidableEq κ] (s : Finset κ) (f : ι → κ → Exp N)
    (hcard : ∀ i, ∑ j ∈ s, (f i j).support.card ≤ N)
    (hinj : Function.Injective fun i => ∑ j ∈ s, parts (f i j)) :
    LinearIndependent R (fun i => ∏ j ∈ s, msym R (f i j)) := by sorry
