-- Prove2me | solution 1 for HigherPythagorean.canonStep_iterate_reaches_root
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:04:38.355667+00:00
-- url     : https://prove2.me/submissions/8f76a7ce-dbb0-48e5-9f95-47313e43579b

-- Sol generated from Shared/HigherPythagorean/CanonicalTree.lean
import Mathlib
import Definitions.Def_Shared_HigherPythagorean_CanonicalTree
import Definitions.Def_Shared_HigherPythagorean_LorentzCore
import Definitions.Def_Shared_HigherPythagorean_QuadrupleGroupoid
import Definitions.Def_Shared_HigherPythagorean_QuadrupleTree
import Definitions.Def_Shared_Ispythquadruple_IsPythQuadruple
import Theorems.Thm_HigherPythagorean_canonStep_isNode
import Theorems.Thm_HigherPythagorean_qk_pos

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




/-- Above height one the canonical parent map strictly decreases the height. -/
theorem canonStep_height_lt {p : Quad} (h : IsNode p) (hd : 1 < p.2.2.2) :
    (canonStep p).2.2.2 < p.2.2.2 := by
  obtain ⟨a, b, c, d⟩ := p
  obtain ⟨ha, hb, hc, hd0, hpyth, hcont⟩ := h
  dsimp only at ha hb hc hd0 hpyth hcont
  replace hd : 1 < d := hd
  have hk := qk_pos ha hb hc hd hpyth hcont
  show d - qk a b c d < d
  omega






open HigherPythagorean in
theorem solution:
    ∀ (N : ℕ) (p : Quad), p.2.2.2.toNat ≤ N → IsNode p →
      ∃ k : ℕ, IsNode (canonStep^[k] p) ∧ (canonStep^[k] p).2.2.2 = 1 := by
  intro N
  induction N with
  | zero =>
      intro p hN h
      exact absurd h.2.2.2.1 (by omega)
  | succ N ih =>
      intro p hN h
      rcases eq_or_lt_of_le (show (1 : ℤ) ≤ p.2.2.2 from h.2.2.2.1) with hd1 | hd1
      · exact ⟨0, by simpa using h, by simpa using hd1.symm⟩
      · have hnode := canonStep_isNode h
        have hlt := canonStep_height_lt h hd1
        have hpos : 0 < (canonStep p).2.2.2 := hnode.2.2.2.1
        have hsmall : (canonStep p).2.2.2.toNat ≤ N := by omega
        obtain ⟨k, hk1, hk2⟩ := ih (canonStep p) hsmall hnode
        exact ⟨k + 1, by rwa [Function.iterate_succ_apply], by
          rw [Function.iterate_succ_apply]; exact hk2⟩
