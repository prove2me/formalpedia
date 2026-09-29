-- Prove2me | solution 1 for HigherPythagorean.canonStep_isNode
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:59:35.762601+00:00
-- url     : https://prove2.me/submissions/4012c971-a786-45f9-b4a8-51aa6bd02c6e

-- Sol generated from Shared/HigherPythagorean/CanonicalTree.lean
import Mathlib
import Definitions.Def_Shared_HigherPythagorean_CanonicalTree
import Definitions.Def_Shared_HigherPythagorean_LorentzCore
import Definitions.Def_Shared_HigherPythagorean_QuadrupleGroupoid
import Definitions.Def_Shared_HigherPythagorean_QuadrupleTree
import Definitions.Def_Shared_Ispythquadruple_IsPythQuadruple
import Theorems.Thm_HigherPythagorean_content_abs3
import Theorems.Thm_HigherPythagorean_content_move
import Theorems.Thm_HigherPythagorean_qmove_pyth
import Theorems.Thm_HigherPythagorean_sub_qk_pos

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










open HigherPythagorean in
theorem solution{p : Quad} (h : IsNode p) : IsNode (canonStep p) := by
  obtain ⟨a, b, c, d⟩ := p
  obtain ⟨ha, hb, hc, hd, hpyth, hcont⟩ := h
  refine ⟨abs_nonneg _, abs_nonneg _, abs_nonneg _, ?_, ?_, ?_⟩
  · exact sub_qk_pos ha hb hc hd hpyth
  · have hmove := qmove_pyth hpyth
    unfold IsPythQuadruple at hmove ⊢
    simp only [canonStep]
    rw [sq_abs, sq_abs, sq_abs]
    exact hmove
  · simp only [canonStep]
    rw [content_abs3, content_move]
    exact hcont
