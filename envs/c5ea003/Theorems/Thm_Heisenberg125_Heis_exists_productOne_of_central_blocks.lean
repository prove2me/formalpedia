-- Prove2me | Theorems.Thm_Heisenberg125_Heis_exists_productOne_of_central_blocks
-- name    : Heisenberg125.Heis.exists_productOne_of_central_blocks
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:48:18.192726+00:00
-- url     : https://prove2.me/theorems/363f7df3-ce5d-4aa0-b8e1-a1e82336f15b
-- title:
--   Block criterion.
-- statement:
--   **Block criterion.**  If a sequence is cut into at least `p` nonempty
--   consecutive blocks whose products are all central, then it has a nonempty
--   product-one subsequence: the "quotient sequence" of block products lives in the
--   centre `C_p`, where the pigeonhole applies.
--
--   ```lean
--   theorem Heisenberg125.Heis.exists_productOne_of_central_blocks[NeZero p] {Bs : List (List (Heis p))}
--       (hne : ∀ B ∈ Bs, B ≠ []) (hcen : ∀ B ∈ Bs, (B.prod).a = 0 ∧ (B.prod).b = 0)
--       (hlen : p ≤ Bs.length) :
--       ∃ T : List (Heis p), T.Sublist Bs.flatten ∧ T ≠ [] ∧ T.prod = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/Heisenberg125/BlockCriterion.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/Heisenberg125/BlockCriterion.lean#L55

-- Thm stub generated from Algebra/Heisenberg125/BlockCriterion.lean
import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_CosetBound
/-
# A product-one criterion: reduction to the abelian quotient

The paper under study reduces the non-commutative product-one problem for
`H_{p^3}` to additive combinatorics over `F_p^2`.  Here we formalise the
complementary half of that reduction: the passage from the *centre*.

**Theorem** (`exists_productOne_of_central_blocks`).  If a sequence is split
into `p` nonempty consecutive blocks, each of which has *central* product, then
it has a nonempty product-one subsequence.

The proof is a pigeonhole on the prefix products of the block products: those
prefix products all lie in the centre `⟨v⟩ ≅ C_p`, of which there are only `p`,
so two of the `p + 1` prefixes coincide and the blocks in between multiply to
`1`.

We also record that product-one-freeness only depends on the multiset of the
sequence (`ProductOneFree.perm`), so the "consecutive blocks" hypothesis costs
no generality once one is allowed to reorder.
-/

open Heisenberg125

variable {G : Type*} [Group G]



open Heis

variable {p : ℕ}

theorem Heisenberg125.Heis.exists_productOne_of_central_blocks[NeZero p] {Bs : List (List (Heis p))}
    (hne : ∀ B ∈ Bs, B ≠ []) (hcen : ∀ B ∈ Bs, (B.prod).a = 0 ∧ (B.prod).b = 0)
    (hlen : p ≤ Bs.length) :
    ∃ T : List (Heis p), T.Sublist Bs.flatten ∧ T ≠ [] ∧ T.prod = 1 := by sorry
