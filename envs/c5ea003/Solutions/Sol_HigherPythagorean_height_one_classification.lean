-- Prove2me | solution 1 for HigherPythagorean.height_one_classification
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:04:42.463016+00:00
-- url     : https://prove2.me/submissions/3ff36e5c-044d-4e8b-851c-86b7a89c2a28

-- Sol generated from Shared/HigherPythagorean/CanonicalTree.lean
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










open HigherPythagorean in
theorem solution{p : Quad} (h : IsNode p) (hd : p.2.2.2 = 1) :
    p = (1, 0, 0, 1) ∨ p = (0, 1, 0, 1) ∨ p = (0, 0, 1, 1) := by
  obtain ⟨a, b, c, d⟩ := p
  obtain ⟨ha, hb, hc, hd0, hpyth, hcont⟩ := h
  simp only at hd
  subst hd
  unfold IsPythQuadruple at hpyth
  have h' : a ^ 2 + b ^ 2 + c ^ 2 = 1 := by linarith
  have ha1 : a ≤ 1 := by nlinarith
  have hb1 : b ≤ 1 := by nlinarith
  have hc1 : c ≤ 1 := by nlinarith
  have hcase : (a = 1 ∧ b = 0 ∧ c = 0) ∨ (a = 0 ∧ b = 1 ∧ c = 0) ∨ (a = 0 ∧ b = 0 ∧ c = 1) := by
    interval_cases a <;> interval_cases b <;> interval_cases c <;> simp_all
  rcases hcase with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)
