-- Prove2me | Theorems.Thm_HigherPythagorean_quad_one_descent_family
-- name    : HigherPythagorean.quad_one_descent_family
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:41:31.1128+00:00
-- url     : https://prove2.me/theorems/e0b0c9af-c800-4c7c-9be9-d5d0058accdc
-- title:
--   Unique parent for the family `(2m, 2m, 2mÂ²â1, 2mÂ²+1)`.
-- statement:
--   **Unique parent for the family `(2m, 2m, 2mÂ²â1, 2mÂ²+1)`.**  In contrast with
--   `quad_two_parents_family`, these nodes admit exactly one descent.
--
--   ```lean
--   theorem HigherPythagorean.quad_one_descent_family(m : ℤ) (hm : 2 ≤ m) :
--       ∃! p : ℤ × ℤ × ℤ, (IsSign p.1 ∧ IsSign p.2.1 ∧ IsSign p.2.2) ∧
--         Descends p.1 p.2.1 p.2.2 (2 * m) (2 * m) (2 * m ^ 2 - 1) (2 * m ^ 2 + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/HigherPythagorean/HarmonicLaw.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/HigherPythagorean/HarmonicLaw.lean#L128

-- Thm stub generated from Shared/HigherPythagorean/HarmonicLaw.lean
import Mathlib
import Definitions.Def_Shared_HigherPythagorean_BranchingContrast
import Definitions.Def_Shared_HigherPythagorean_LorentzCore
import Definitions.Def_Shared_HigherPythagorean_QuadrupleTree
import Definitions.Def_Shared_Ispythquadruple_IsPythQuadruple

/-!
# The harmonic branching law for Pythagorean quadruples

`BranchingContrast` shows that a Pythagorean quadruple has at most two parents.  Here we
determine *exactly when* the second parent exists, and the answer is an Egyptian-fraction
("harmonic") law:

> the reflection move with a minus sign on the coordinate `a` descends **iff** `1/a > 1/b + 1/c`.

This is the dimension-three replacement for the (empty) second-parent condition of the Berggren
tree, and it explains all the phenomena observed in dimension three:

* `quad_minus_descent_iff` / `quad_minus_descent_iff_rat` : the law, in integral and harmonic form.
* `harmonic_law_at_most_one_index` : the harmonic inequality can hold for at most one coordinate
  (a two-line proof of the "at most two parents" bound).
* `quad_neutral_move_iff` : the boundary case `1/a = 1/b + 1/c` gives a *height preserving*
  ("horizontal") move — a phenomenon that does not exist for triples (`triple_no_neutral_move`),
  realised e.g. by the quadruple `(1,2,2,3)`.
* `quad_one_descent_family` : the family `(2m, 2m, 2m²−1, 2m²+1)` has a **unique** parent, while
  `(1, 2m, 2m², 2m²+1)` has two; hence (`quad_branching_not_constant`) the branching number of
  the quadruple graph is genuinely non-constant, taking both possible values infinitely often.
-/

open HigherPythagorean

/-! ## The harmonic law -/




/-! ## Neutral (height preserving) moves -/




/-! ## A family with a unique parent -/

theorem HigherPythagorean.quad_one_descent_family(m : ℤ) (hm : 2 ≤ m) :
    ∃! p : ℤ × ℤ × ℤ, (IsSign p.1 ∧ IsSign p.2.1 ∧ IsSign p.2.2) ∧
      Descends p.1 p.2.1 p.2.2 (2 * m) (2 * m) (2 * m ^ 2 - 1) (2 * m ^ 2 + 1) := by sorry
