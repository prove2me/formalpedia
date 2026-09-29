-- Prove2me | Definitions.Def_Shared_HigherPythagorean_BranchingContrast
-- name    : Shared_HigherPythagorean_BranchingContrast
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:55:39.494446+00:00
-- url     : https://prove2.me/theorems/89a0941e-8d30-492f-9ab0-b6ce9b5eb832
-- title:
--   Aether Catalog definitions — Shared_HigherPythagorean_BranchingContrast
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.HigherPythagorean.BranchingContrast`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/HigherPythagorean/BranchingContrast.lean by skeleton subtraction
import Mathlib
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

namespace HigherPythagorean

/-- `e` is a sign. -/
def IsSign (e : ℤ) : Prop := e = 1 ∨ e = -1

/-! ## Triples: exactly one descent, hence a tree -/

/-- The sign pattern `(e₁,e₂)` descends at the triple `(a,b,c)` iff the reflected height
`3c − 2(e₁a+e₂b)` is smaller than `c`, i.e. iff `e₁a+e₂b > c`. -/
def TDescends (e₁ e₂ a b c : ℤ) : Prop := c < e₁ * a + e₂ * b





/-! ## Quadruples: at most two descents -/

/-- The sign pattern `(e₁,e₂,e₃)` descends at the quadruple `(a,b,c,d)` iff the reflected height
`2d − (e₁a+e₂b+e₃c)` is smaller than `d`. -/
def Descends (e₁ e₂ e₃ a b c d : ℤ) : Prop := d < e₁ * a + e₂ * b + e₃ * c






/-! ## Content shortcuts -/



/-! ## An infinite family of quadruples with two parents -/









/-! ## Integral form of the growth constants -/



end HigherPythagorean


