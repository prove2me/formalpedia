-- Prove2me | Definitions.Def_Shared_HigherPythagorean_CanonicalTree
-- name    : Shared_HigherPythagorean_CanonicalTree
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:55:50.427108+00:00
-- url     : https://prove2.me/theorems/b197263d-75b8-4de9-9d8f-0e3b297d289e
-- title:
--   Aether Catalog definitions — Shared_HigherPythagorean_CanonicalTree
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.HigherPythagorean.CanonicalTree`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/HigherPythagorean/CanonicalTree.lean by skeleton subtraction
import Mathlib
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

namespace HigherPythagorean

/-- A node: a primitive Pythagorean quadruple in the positive cone. -/
def IsNode (p : Quad) : Prop :=
  0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2.1 ∧ 0 < p.2.2.2 ∧
    IsPythQuadruple p.1 p.2.1 p.2.2.1 p.2.2.2 ∧ content p.1 p.2.1 p.2.2.1 p.2.2.2 = 1

/-- The canonical parent map: the all-plus reflection followed by taking absolute values. -/
def canonStep (p : Quad) : Quad :=
  (|p.1 - qk p.1 p.2.1 p.2.2.1 p.2.2.2|, |p.2.1 - qk p.1 p.2.1 p.2.2.1 p.2.2.2|,
    |p.2.2.1 - qk p.1 p.2.1 p.2.2.1 p.2.2.2|, p.2.2.2 - qk p.1 p.2.1 p.2.2.1 p.2.2.2)







end HigherPythagorean


