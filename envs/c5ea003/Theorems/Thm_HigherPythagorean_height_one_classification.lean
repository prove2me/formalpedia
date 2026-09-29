-- Prove2me | Theorems.Thm_HigherPythagorean_height_one_classification
-- name    : HigherPythagorean.height_one_classification
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:41:41.225728+00:00
-- url     : https://prove2.me/theorems/e6c1699c-c109-4967-bc1f-3a075ac399cb
-- title:
--   The nodes of height one are exactly the three permutations of the root `(1,0,0,1)`.
-- statement:
--   The nodes of height one are exactly the three permutations of the root `(1,0,0,1)`.
--
--   ```lean
--   theorem HigherPythagorean.height_one_classification{p : Quad} (h : IsNode p) (hd : p.2.2.2 = 1) :
--       p = (1, 0, 0, 1) ∨ p = (0, 1, 0, 1) ∨ p = (0, 0, 1, 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/HigherPythagorean/CanonicalTree.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/HigherPythagorean/CanonicalTree.lean#L61

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

theorem HigherPythagorean.height_one_classification{p : Quad} (h : IsNode p) (hd : p.2.2.2 = 1) :
    p = (1, 0, 0, 1) ∨ p = (0, 1, 0, 1) ∨ p = (0, 0, 1, 1) := by sorry
