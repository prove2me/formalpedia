-- Prove2me | Theorems.Thm_BerggrenRationalStars_no_line_through_irrational
-- name    : BerggrenRationalStars.no_line_through_irrational
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:35:53.824733+00:00
-- url     : https://prove2.me/theorems/1420c7a0-c53b-481a-88de-b7fd25927d07
-- title:
--   No star at an irrational point.
-- statement:
--   **No star at an irrational point.** Two Berggren nodes on a common Euclidean line through an
--   irrational ideal point `α` coincide. (For a rational ideal point the same line carries
--   infinitely many nodes, by `BerggrenRationalStars.isSeed_along_unit_ray`.)
--
--   ```lean
--   theorem BerggrenRationalStars.no_line_through_irrational(a : ℝ) (ha : Irrational a) (m n m' n' : ℕ)
--       (hm : 0 < m) (hm' : 0 < m') (c : ℝ)
--       (h1 : (hpoint m n hm).re = a + c * (hpoint m n hm).im)
--       (h2 : (hpoint m' n' hm').re = a + c * (hpoint m' n' hm').im) :
--       m = m' ∧ n = n' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenStars/StarHierarchy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenStars/StarHierarchy.lean#L26

-- Thm stub generated from Cryptography/BerggrenStars/StarHierarchy.lean
import Mathlib
import Definitions.Def_Cryptography_BerggrenStars_HypercycleStars
import Definitions.Def_Cryptography_BerggrenStars_RationalStars

/-!
# Why the stars sit at rationals, and why only finitely many of them are visible

Two complementary facts finish the explanation of the star map of the Berggren tree.

## Main results

* `no_line_through_irrational` : **there is no star at an irrational boundary point.** If two
  Berggren nodes lie on one Euclidean line through an ideal point `α` with `α` irrational, then
  they are the same node. Radial lines can only emanate from *rational* boundary points; the
  irrational directions of the picture carry no line at all, however dense the nodes are near
  them.
* `finite_visible_stars` : **the visible hierarchy is finite.** For every resolution threshold
  `ε > 0` only finitely many rationals `p/q ∈ [0,1]` have a star of resolution
  `δ(p/q) = starGapNum p q / q ≥ ε`. Combined with `BerggrenRationalStars.visible_rationals`,
  which computes the list for `ε = 2/5`, this says the star map has a discrete, computable
  hierarchy of visible directions rather than a continuum of them.
-/

open BerggrenRationalStars

open BerggrenHypercycleStars

theorem BerggrenRationalStars.no_line_through_irrational(a : ℝ) (ha : Irrational a) (m n m' n' : ℕ)
    (hm : 0 < m) (hm' : 0 < m') (c : ℝ)
    (h1 : (hpoint m n hm).re = a + c * (hpoint m n hm).im)
    (h2 : (hpoint m' n' hm').re = a + c * (hpoint m' n' hm').im) :
    m = m' ∧ n = n' := by sorry
