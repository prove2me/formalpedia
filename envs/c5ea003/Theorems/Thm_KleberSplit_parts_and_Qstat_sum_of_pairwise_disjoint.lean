-- Prove2me | Theorems.Thm_KleberSplit_parts_and_Qstat_sum_of_pairwise_disjoint
-- name    : KleberSplit.parts_and_Qstat_sum_of_pairwise_disjoint
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:43:40.047978+00:00
-- url     : https://prove2.me/theorems/bb9d279c-5720-4300-8c9f-917ddc9e5a7d
-- title:
--   Under pairwise disjointness both `parts` and `Qstat` are additive along a finite sum.
-- statement:
--   Under pairwise disjointness both `parts` and `Qstat` are additive along a finite sum.
--
--   ```lean
--   theorem KleberSplit.parts_and_Qstat_sum_of_pairwise_disjoint{κ : Type*} [DecidableEq κ] (s : Finset κ)
--       (u : κ → Exp N) (h : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → Disjoint (u j).support (u k).support) :
--       parts (∑ j ∈ s, u j) = ∑ j ∈ s, parts (u j) ∧
--         Qstat (∑ j ∈ s, u j) = ∑ j ∈ s, Qstat (u j) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/KleberManyFoldProducts.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/KleberManyFoldProducts.lean#L78

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

theorem KleberSplit.parts_and_Qstat_sum_of_pairwise_disjoint{κ : Type*} [DecidableEq κ] (s : Finset κ)
    (u : κ → Exp N) (h : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → Disjoint (u j).support (u k).support) :
    parts (∑ j ∈ s, u j) = ∑ j ∈ s, parts (u j) ∧
      Qstat (∑ j ∈ s, u j) = ∑ j ∈ s, Qstat (u j) := by sorry
