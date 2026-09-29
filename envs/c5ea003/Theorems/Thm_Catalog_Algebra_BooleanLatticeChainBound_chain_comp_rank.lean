-- Prove2me | Theorems.Thm_Catalog_Algebra_BooleanLatticeChainBound_chain_comp_rank
-- name    : Catalog.Algebra.BooleanLatticeChainBound.chain_comp_rank
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:27:21.36432+00:00
-- url     : https://prove2.me/theorems/c7305f75-44df-46b8-87a3-25a8e4d98a90
-- title:
--   Composing a strictly increasing chain of length `2^d` with the rank function of `B d`
-- statement:
--   Composing a strictly increasing chain of length `2^d` with the rank function of `B d`
--   produces an injective, containment-preserving map from `B d`.
--
--   ```lean
--   theorem Catalog.Algebra.BooleanLatticeChainBound.chain_comp_rank{d : ℕ} {g : ℕ → Finset (Fin n)}
--       (hg : ∀ i j, i < j → j < 2 ^ d → g i ⊂ g j) :
--       Function.Injective (fun S : Finset (Fin d) => g (rank d S)) ∧
--         ∀ S T : Finset (Fin d), S ⊆ T → g (rank d S) ⊆ g (rank d T) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/BooleanLatticeChainBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/BooleanLatticeChainBound.lean#L110

-- Thm stub generated from Algebra/BooleanLatticeChainBound.lean
import Mathlib
import Definitions.Def_Algebra_BooleanLatticeChainBound
/-
# Forbidden Boolean-lattice subposets: the chain bound and its sharpening

This file develops, from scratch, a formal framework for the extremal problem

  `La(n, B_d) = max { |F| : F ⊆ 2^[n], F contains no (weak) copy of the Boolean lattice B_d }`

and proves the classical *chain bound* `La(n, B_d) ≤ (2^d - 1) * C(n, ⌊n/2⌋)`
together with a number of complementary results relevant to the conjecture
`La(n, B_d) ≤ (d + c) * C(n, ⌊n/2⌋)` for an absolute constant `c`.

## Main definitions

* `HasBdCopy d F` : the family `F` of subsets of `Fin n` contains a *weak* copy of the
  `d`-dimensional Boolean lattice, i.e. an injective, containment-preserving map
  `Finset (Fin d) → F`.
* `BdFree d F`    : `F` contains no such copy.
* `HasChain k F`  : `F` contains a strictly increasing chain of `k` sets.
* `La n d`        : the extremal function, the supremum of `|F|` over `B_d`-free `F`.

## Main results

* `hasBdCopy_of_hasChain`    : a chain of `2^d` sets already yields a weak copy of `B_d`.
* `lubell_le_of_no_chain`    : the Lubell mass of a `(k+1)`-chain-free family is at most `k`
  (a Mirsky-type induction feeding into the LYM inequality). This is strictly stronger
  than the corresponding cardinality bound.
* `card_le_of_bdFree`        : the chain bound `|F| ≤ (2^d - 1) * C(n, ⌊n/2⌋)`.
* `La_le_chain_bound`        : `La n d ≤ (2^d - 1) * C(n, ⌊n/2⌋)`.
* `La_one`                   : `La n 1 = C(n, ⌊n/2⌋)` (Sperner's theorem, both directions).
* `La_le_height_bound`       : `La n d ≤ (n+1) * C(n, ⌊n/2⌋)`, hence the conjectured bound
  `(d + 1) * C(n, ⌊n/2⌋)` holds unconditionally whenever `n ≤ d`.
* `La_three_le_four_of_le_eight` : the conjectured `d = 3` bound `La n 3 ≤ 4 * C(n, ⌊n/2⌋)`
  holds for every `n ≤ 8`.
* `La_ge_consecutive_levels` : the lower bound coming from `d` consecutive levels,
  `La n d ≥ ∑_{i=a}^{a+d-1} C(n, i)`.
* `hasBdCopy_succ_of_stacked` and `hasBdCopy_succ_of_parallel_chains` : a *doubling*
  criterion showing that a `B_{d+1}` copy already arises from two "parallel" `B_d` copies,
  a configuration strictly weaker than a single long chain.
-/


open Catalog.Algebra.BooleanLatticeChainBound

open Finset

/-! ## The central binomial coefficient -/




/-! ## Weak copies of the Boolean lattice -/

variable {n : ℕ}





/-! ## A linear extension of `B d` -/






/-! ## Chains produce Boolean-lattice copies -/

theorem Catalog.Algebra.BooleanLatticeChainBound.chain_comp_rank{d : ℕ} {g : ℕ → Finset (Fin n)}
    (hg : ∀ i j, i < j → j < 2 ^ d → g i ⊂ g j) :
    Function.Injective (fun S : Finset (Fin d) => g (rank d S)) ∧
      ∀ S T : Finset (Fin d), S ⊆ T → g (rank d S) ⊆ g (rank d T) := by sorry
