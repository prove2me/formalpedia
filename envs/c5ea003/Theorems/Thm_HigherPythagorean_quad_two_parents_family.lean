-- Prove2me | Theorems.Thm_HigherPythagorean_quad_two_parents_family
-- name    : HigherPythagorean.quad_two_parents_family
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:41:46.429195+00:00
-- url     : https://prove2.me/theorems/bdd512ee-49e1-46a6-a59c-853868e05087
-- title:
--   The quadruple graph is not a tree.
-- statement:
--   **The quadruple graph is not a tree.**  For every `m â¥ 2` the primitive quadruple
--   `(1, 2m, 2mÂ², 2mÂ²+1)` has two distinct descents, landing on two primitive quadruples of
--   different (strictly smaller) heights, both reachable from the root.  In particular no
--   consistent notion of "the" parent exists, and the graph carries infinitely many cycles.
--
--   ```lean
--   theorem HigherPythagorean.quad_two_parents_family(m : ℤ) (hm : 2 ≤ m) :
--       IsPrimQuad 1 (2 * m) (2 * m ^ 2) (2 * m ^ 2 + 1) ∧
--       Descends 1 1 1 1 (2 * m) (2 * m ^ 2) (2 * m ^ 2 + 1) ∧
--       Descends (-1) 1 1 1 (2 * m) (2 * m ^ 2) (2 * m ^ 2 + 1) ∧
--       IsPrimQuad (2 * m - 1) 0 (2 * m ^ 2 - 2 * m) (2 * m ^ 2 - 2 * m + 1) ∧
--       IsPrimQuad (2 * m - 1) 2 (2 * m ^ 2 - 2 * m + 2) (2 * m ^ 2 - 2 * m + 3) ∧
--       Reach (2 * m - 1) 0 (2 * m ^ 2 - 2 * m) (2 * m ^ 2 - 2 * m + 1) ∧
--       Reach (2 * m - 1) 2 (2 * m ^ 2 - 2 * m + 2) (2 * m ^ 2 - 2 * m + 3) ∧
--       (2 * m ^ 2 - 2 * m + 1 : ℤ) ≠ 2 * m ^ 2 - 2 * m + 3 := by sorry
--
--   /-! ## Integral form of the growth constants -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/HigherPythagorean/BranchingContrast.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/HigherPythagorean/BranchingContrast.lean#L208

-- Thm stub generated from Shared/HigherPythagorean/BranchingContrast.lean
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







/-! ## Content shortcuts -/



/-! ## An infinite family of quadruples with two parents -/

theorem HigherPythagorean.quad_two_parents_family(m : ℤ) (hm : 2 ≤ m) :
    IsPrimQuad 1 (2 * m) (2 * m ^ 2) (2 * m ^ 2 + 1) ∧
    Descends 1 1 1 1 (2 * m) (2 * m ^ 2) (2 * m ^ 2 + 1) ∧
    Descends (-1) 1 1 1 (2 * m) (2 * m ^ 2) (2 * m ^ 2 + 1) ∧
    IsPrimQuad (2 * m - 1) 0 (2 * m ^ 2 - 2 * m) (2 * m ^ 2 - 2 * m + 1) ∧
    IsPrimQuad (2 * m - 1) 2 (2 * m ^ 2 - 2 * m + 2) (2 * m ^ 2 - 2 * m + 3) ∧
    Reach (2 * m - 1) 0 (2 * m ^ 2 - 2 * m) (2 * m ^ 2 - 2 * m + 1) ∧
    Reach (2 * m - 1) 2 (2 * m ^ 2 - 2 * m + 2) (2 * m ^ 2 - 2 * m + 3) ∧
    (2 * m ^ 2 - 2 * m + 1 : ℤ) ≠ 2 * m ^ 2 - 2 * m + 3 := by sorry
