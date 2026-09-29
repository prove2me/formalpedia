-- Prove2me | Theorems.Thm_HigherPythagorean_content_eq_one_of_fst_one
-- name    : HigherPythagorean.content_eq_one_of_fst_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:41:51.180812+00:00
-- url     : https://prove2.me/theorems/97afe52c-1746-4040-ba56-cc906efa4b44
-- title:
--   Content eq one of fst one
-- statement:
--   Formal statement of `HigherPythagorean.content_eq_one_of_fst_one` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem HigherPythagorean.content_eq_one_of_fst_one(b c d : ℤ) : content 1 b c d = 1 := by sorry
--
--   /-! ## An infinite family of quadruples with two parents -/
--
--
--
--
--
--
--
--
--
--   /-! ## Integral form of the growth constants -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/HigherPythagorean/BranchingContrast.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/HigherPythagorean/BranchingContrast.lean#L132

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

theorem HigherPythagorean.content_eq_one_of_fst_one(b c d : ℤ) : content 1 b c d = 1 := by sorry
