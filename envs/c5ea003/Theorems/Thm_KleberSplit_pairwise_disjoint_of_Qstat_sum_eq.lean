-- Prove2me | Theorems.Thm_KleberSplit_pairwise_disjoint_of_Qstat_sum_eq
-- name    : KleberSplit.pairwise_disjoint_of_Qstat_sum_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:43:32.494171+00:00
-- url     : https://prove2.me/theorems/168579dc-e860-4d72-b702-13b21dabf2d4
-- title:
--   Equality in the superadditivity of `Qstat` forces pairwise disjoint supports.
-- statement:
--   Equality in the superadditivity of `Qstat` forces pairwise disjoint supports.
--
--   ```lean
--   theorem KleberSplit.pairwise_disjoint_of_Qstat_sum_eq{κ : Type*} [DecidableEq κ] (s : Finset κ)
--       (u : κ → Exp N) (h : Qstat (∑ j ∈ s, u j) = ∑ j ∈ s, Qstat (u j)) :
--       ∀ j ∈ s, ∀ k ∈ s, j ≠ k → Disjoint (u j).support (u k).support := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/KleberManyFoldProducts.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/KleberManyFoldProducts.lean#L54

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

theorem KleberSplit.pairwise_disjoint_of_Qstat_sum_eq{κ : Type*} [DecidableEq κ] (s : Finset κ)
    (u : κ → Exp N) (h : Qstat (∑ j ∈ s, u j) = ∑ j ∈ s, Qstat (u j)) :
    ∀ j ∈ s, ∀ k ∈ s, j ≠ k → Disjoint (u j).support (u k).support := by sorry
