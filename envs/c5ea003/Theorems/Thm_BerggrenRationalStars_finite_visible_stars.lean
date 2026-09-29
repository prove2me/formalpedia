-- Prove2me | Theorems.Thm_BerggrenRationalStars_finite_visible_stars
-- name    : BerggrenRationalStars.finite_visible_stars
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:35:43.231229+00:00
-- url     : https://prove2.me/theorems/51bdc342-a2fd-4d98-864c-ff5198a1fde7
-- title:
--   Only finitely many stars are visible at any resolution.
-- statement:
--   **Only finitely many stars are visible at any resolution.** For each `ε > 0` there are only
--   finitely many boundary rationals `p/q` of `[0,1]` whose star has resolution at least `ε`.
--
--   ```lean
--   theorem BerggrenRationalStars.finite_visible_stars(eps : ℝ) (heps : 0 < eps) :
--       {pq : ℕ × ℕ | 0 < pq.2 ∧ pq.1 ≤ pq.2 ∧ eps ≤ (starGapNum pq.1 pq.2 : ℝ) / pq.2}.Finite := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/BerggrenStars/StarHierarchy.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/BerggrenStars/StarHierarchy.lean#L60

-- Thm stub generated from Cryptography/BerggrenStars/StarHierarchy.lean
import Mathlib
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

theorem BerggrenRationalStars.finite_visible_stars(eps : ℝ) (heps : 0 < eps) :
    {pq : ℕ × ℕ | 0 < pq.2 ∧ pq.1 ≤ pq.2 ∧ eps ≤ (starGapNum pq.1 pq.2 : ℝ) / pq.2}.Finite := by sorry
