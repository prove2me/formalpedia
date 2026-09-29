-- Prove2me | solution 1 for HigherPythagorean.descend_at_most_one_minus
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:04:41.019661+00:00
-- url     : https://prove2.me/submissions/b9fcdd87-b2d4-483e-a1c9-e73bb7686eba

-- Sol generated from Shared/HigherPythagorean/BranchingContrast.lean
import Mathlib
import Definitions.Def_Shared_HigherPythagorean_BranchingContrast
import Definitions.Def_Shared_HigherPythagorean_LorentzCore
import Definitions.Def_Shared_HigherPythagorean_QuadrupleTree
import Definitions.Def_Shared_Ispythquadruple_IsPythQuadruple

/-!
# Branching: why the Berggren tree is a tree in dimension 2 and **not** in dimension 3

A *descent* at a node is a sign pattern `ε ∈ {±1}ⁿ` for which the all-ones reflection move
strictly decreases the height.  Parents in a Berggren-type tree are exactly descents, so a node
has a unique parent iff it admits exactly one descent.

Main results.

* `triple_unique_descent` : a primitive Pythagorean triple with positive legs admits **exactly one**
  descent, namely `ε = (+,+)`.  This is the structural reason the Berggren graph is a *tree*.
* `quad_at_most_two_descents` : a Pythagorean quadruple admits at most **two** descents
  (`ε = (+,+,+)` and at most one pattern with a single minus sign).
* `quad_two_parents_family` : for every `m ≥ 2` the primitive quadruple `(1, 2m, 2m², 2m²+1)`
  really has two descents, landing on two *distinct* primitive quadruples of strictly smaller
  height, both of which are reachable from the root.  Hence the quadruple graph contains
  infinitely many nodes with two parents: it is **not** a tree.
* `triple_height_annulus`, `quad_height_annulus` : the exact integral form of the growth
  constants `3+2√2 = (1+√2)²` (triples, silver ratio) and `2+√3` (quadruples).
-/

open HigherPythagorean


/-! ## Triples: exactly one descent, hence a tree -/






/-! ## Quadruples: at most two descents -/



/-- Each space coordinate of a Pythagorean quadruple is at most the height. -/
lemma coord_le_height {a b c d : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 < d)
    (h : IsPythQuadruple a b c d) : a ≤ d ∧ b ≤ d ∧ c ≤ d := by
  unfold IsPythQuadruple at h
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩




/-! ## Content shortcuts -/



/-! ## An infinite family of quadruples with two parents -/









/-! ## Integral form of the growth constants -/




open HigherPythagorean in
theorem solution{a b c d e₁ e₂ e₃ : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 < d) (h : IsPythQuadruple a b c d) (h1 : IsSign e₁) (h2 : IsSign e₂) (h3 : IsSign e₃)
    (hdes : Descends e₁ e₂ e₃ a b c d) :
    e₁ = 1 ∧ e₂ = 1 ∨ e₁ = 1 ∧ e₃ = 1 ∨ e₂ = 1 ∧ e₃ = 1 := by
  obtain ⟨had, hbd, hcd⟩ := coord_le_height ha hb hc hd h
  unfold Descends at hdes
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> rcases h3 with rfl | rfl
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · exfalso; linarith
  · exact Or.inr (Or.inr ⟨rfl, rfl⟩)
  · exfalso; linarith
  · exfalso; linarith
  · exfalso; linarith
