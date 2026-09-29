-- Prove2me | Theorems.Thm_HigherPythagorean_canonStep_iterate_reaches_root
-- name    : HigherPythagorean.canonStep_iterate_reaches_root
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:41:03.303463+00:00
-- url     : https://prove2.me/theorems/8209bc95-dc24-4ef6-be5b-3bf494e18171
-- title:
--   The canonical parent map is well founded.
-- statement:
--   **The canonical parent map is well founded.**  Finitely many canonical steps take any node to
--   a node of height one, i.e. to a permutation of the root; the canonical parent edges therefore
--   form a spanning tree of the quadruple graph rooted at `(1,0,0,1)`.
--
--   ```lean
--   theorem HigherPythagorean.canonStep_iterate_reaches_root:
--       ∀ (N : ℕ) (p : Quad), p.2.2.2.toNat ≤ N → IsNode p →
--         ∃ k : ℕ, IsNode (canonStep^[k] p) ∧ (canonStep^[k] p).2.2.2 = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/HigherPythagorean/CanonicalTree.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/HigherPythagorean/CanonicalTree.lean#L86

-- Thm stub generated from Shared/HigherPythagorean/CanonicalTree.lean
import Mathlib
import Definitions.Def_Shared_HigherPythagorean_CanonicalTree
import Definitions.Def_Shared_HigherPythagorean_LorentzCore
import Definitions.Def_Shared_HigherPythagorean_QuadrupleGroupoid
import Definitions.Def_Shared_HigherPythagorean_QuadrupleTree
import Definitions.Def_Shared_Ispythquadruple_IsPythQuadruple

/-!
# The canonical spanning tree of the Pythagorean quadruple graph

The quadruple graph is not a tree (`BranchingContrast.quad_two_parents_family`), but the
all-plus reflection singles out a *canonical* parent, and this canonical parent map does define
a rooted tree structure: it preserves primitivity, strictly decreases the height above height
one, and its iterates reach a node of height one in finitely many steps; the nodes of height one
are exactly the three permutations of the root `(1,0,0,1)`.

* `canonStep` : the canonical parent map.
* `canonStep_isNode` : it preserves the class of primitive non-negative nodes.
* `canonStep_height_lt` : it strictly decreases the height above height one.
* `height_one_classification` : the height-one nodes are the permutations of `(1,0,0,1)`.
* `canonStep_iterate_reaches_root` : finitely many canonical steps reach height one — the
  canonical parent map is well-founded, so the graph has a canonical spanning tree.
-/

open HigherPythagorean

theorem HigherPythagorean.canonStep_iterate_reaches_root:
    ∀ (N : ℕ) (p : Quad), p.2.2.2.toNat ≤ N → IsNode p →
      ∃ k : ℕ, IsNode (canonStep^[k] p) ∧ (canonStep^[k] p).2.2.2 = 1 := by sorry
