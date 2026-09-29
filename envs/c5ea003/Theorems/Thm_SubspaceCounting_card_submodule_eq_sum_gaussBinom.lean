-- Prove2me | Theorems.Thm_SubspaceCounting_card_submodule_eq_sum_gaussBinom
-- name    : SubspaceCounting.card_submodule_eq_sum_gaussBinom
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:52:35.726776+00:00
-- url     : https://prove2.me/theorems/a3d17284-e56e-4b1f-9700-d44989c273e7
-- title:
--   Total subspace count.
-- statement:
--   **Total subspace count.**  The number of subspaces of a finite `K`-vector space of dimension
--   `n` is the Galois number `∑_{k ≤ n} gaussBinom q n k`.
--
--   ```lean
--   theorem SubspaceCounting.card_submodule_eq_sum_gaussBinom:
--       Nat.card (Submodule K V)
--         = ∑ k ∈ Finset.range (finrank K V + 1), gaussBinom (Fintype.card K) (finrank K V) k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/SubspaceCounting.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/SubspaceCounting.lean#L160

-- Thm stub generated from NumberTheory/SubspaceCounting.lean
import Mathlib
import Definitions.Def_NumberTheory_SubspaceCounting
/-
# Counting the subspaces of a finite-dimensional vector space over a finite field

This file proves the classical Gaussian (`q`-binomial) count of subspaces of a finite vector
space, in the form needed for the elementary abelian case of the Hilbert class field descent
picture of `Catalog/NumberTheory/HilbertClassFieldDescent.lean`.

Let `K` be a finite field with `q` elements and `V` a finite `K`-vector space of dimension `n`.

* `gaussBinom q n k` : the Gaussian binomial coefficient
  `∏_{i<k}(q^n - q^i) / ∏_{i<k}(q^k - q^i)`;
* `card_linearIndependent_eq_mul` : linearly independent `k`-tuples of `V` are fibred over the
  `k`-dimensional subspaces, each fibre being the set of bases of that subspace;
* `card_submodule_finrank_mul` : `#{W : dim W = k} * ∏_{i<k}(q^k - q^i) = ∏_{i<k}(q^n - q^i)`;
* `card_submodule_finrank_eq_gaussBinom` : `#{W : dim W = k} = gaussBinom q n k`;
* `card_submodule_eq_sum_gaussBinom` : `#(subspaces of V) = ∑_{k≤n} gaussBinom q n k`;
* `gaussBinom_symm` : `gaussBinom q n k = gaussBinom q n (n - k)` for `k ≤ n`, proved through the
  duality bijection between `k`- and `(n-k)`-dimensional subspaces;
* the specialisations to `V = (ZMod p)^r` used by the class field application.
-/


open Module Finset

open SubspaceCounting






variable (K V : Type*) [Field K] [Fintype K] [AddCommGroup V] [Module K V] [Finite V]

theorem SubspaceCounting.card_submodule_eq_sum_gaussBinom:
    Nat.card (Submodule K V)
      = ∑ k ∈ Finset.range (finrank K V + 1), gaussBinom (Fintype.card K) (finrank K V) k := by sorry
