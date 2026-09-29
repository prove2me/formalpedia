-- Prove2me | solution 1 for HigherPythagorean.content_eq_one_of_fst_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T00:04:39.034762+00:00
-- url     : https://prove2.me/submissions/a179c27f-8717-484f-afda-50eab2161200

-- Sol generated from Shared/HigherPythagorean/BranchingContrast.lean
import Mathlib
import Definitions.Def_Shared_HigherPythagorean_BranchingContrast
import Definitions.Def_Shared_HigherPythagorean_LorentzCore
import Definitions.Def_Shared_HigherPythagorean_QuadrupleTree
import Definitions.Def_Shared_Ispythquadruple_IsPythQuadruple
import Theorems.Thm_HigherPythagorean_content_dvd_fst

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







/-! ## Content shortcuts -/



/-! ## An infinite family of quadruples with two parents -/









/-! ## Integral form of the growth constants -/




open HigherPythagorean in
theorem solution(b c d : ℤ) : content 1 b c d = 1 := by
  have h1 := content_dvd_fst 1 b c d
  have : (content 1 b c d : ℕ) ∣ 1 := by exact_mod_cast h1
  exact Nat.dvd_one.mp this
