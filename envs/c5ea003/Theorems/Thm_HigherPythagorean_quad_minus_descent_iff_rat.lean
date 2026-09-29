-- Prove2me | Theorems.Thm_HigherPythagorean_quad_minus_descent_iff_rat
-- name    : HigherPythagorean.quad_minus_descent_iff_rat
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:42:02.625041+00:00
-- url     : https://prove2.me/theorems/9881a9b1-7e14-4be0-98c9-587dc4e12682
-- title:
--   Harmonic branching law (Egyptian-fraction form).
-- statement:
--   **Harmonic branching law (Egyptian-fraction form).**  The second parent exists exactly when
--   the reciprocal of one leg exceeds the sum of the reciprocals of the other two.
--
--   ```lean
--   theorem HigherPythagorean.quad_minus_descent_iff_rat{a b c d : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
--       (hd : 0 < d) (h : IsPythQuadruple a b c d) :
--       Descends (-1) 1 1 a b c d ↔ (1 : ℚ) / (b : ℚ) + 1 / (c : ℚ) < 1 / (a : ℚ) := by sorry
--
--   /-! ## Neutral (height preserving) moves -/
--
--
--
--
--   /-! ## A family with a unique parent -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/HigherPythagorean/HarmonicLaw.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/HigherPythagorean/HarmonicLaw.lean#L46

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

theorem HigherPythagorean.quad_minus_descent_iff_rat{a b c d : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (h : IsPythQuadruple a b c d) :
    Descends (-1) 1 1 a b c d ↔ (1 : ℚ) / (b : ℚ) + 1 / (c : ℚ) < 1 / (a : ℚ) := by sorry
