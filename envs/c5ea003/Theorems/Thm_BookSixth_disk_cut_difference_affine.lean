-- Prove2me | Theorems.Thm_BookSixth_disk_cut_difference_affine
-- name    : BookSixth.disk_cut_difference_affine
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T02:22:02.282263+00:00
-- url     : https://prove2.me/theorems/325ced96-8073-4eca-a8ab-24eeb21aa9f3
-- title:
--   The difference of two flat-disk cut functions along a line is affine in the line parameter
-- statement:
--   Fix a Euclidean unit line direction `e`, a point `a` on the line, and two flat disks with centres `c₁`, `c₂` and squared radii `r₁²`, `r₂²`. The line cuts out of the disk with centre `cᵢ` and radius `rᵢ` the set of parameters `s` with `fᵢ(s) ≥ 0`, where
--
--       fᵢ(s) = rᵢ² − ‖a + s·e − cᵢ‖₂²
--
--   is the height of the lifted spherical dome over the disk at the point `a + s·e`.
--
--   Expanding the squared norm, the `s²` term carries the coefficient `−∑ e i * e i`, which is **the same for both disks**, so it cancels in the difference `f₁(s) − f₂(s)`. The difference is therefore a genuine **affine function of `s`**:
--
--       f₁(s) − f₂(s) = (r₁² − r₂²) − ‖a − c₁‖₂² + ‖a − c₂‖₂²
--                        − 2s·( e·(a − c₁) − e·(a − c₂) ).
--
--   This is the algebraic core of the Freedman–Skora two-hemisphere argument. When the
--   two hemispheres meet, `f₁(s) = f₂(s) = h²` for a single `s`; because `f₁ − f₂` is affine,
--   its zero set is either empty, a single point, or the whole line. So the two flat disks
--   cut the common line in a controlled way, and the case analysis degenerates to the
--   sub-case in which the slope vanishes and the difference is identically zero.
--
--   Note the hypothesis `(∑ i, e i * e i) = 1` records that `e` is a Euclidean unit vector,
--   not a supremum-norm unit vector.
-- source:
--   **Expansion.** For each `i`,
--
--       (a i + s * e i − c i) * (a i + s * e i − c i)
--         = (a i − c i)² + 2 s e i (a i − c i) + s² (e i)²,
--
--   so after summing, `fᵢ(s)` collects the three terms
--
--       rᵢ² − ‖a − cᵢ‖₂²  −  2s·(e · (a − cᵢ))  −  s²·‖e‖₂².
--
--   The `s²` coefficient `−‖e‖₂²` is independent of `i`, hence it cancels in `f₁ − f₂`.
--
--   **Why it matters.** The hypothesis `he : (∑ i, e i * e i) = 1` fixes `‖e‖₂ = 1`, so the
--   difference is affine with a well-defined linear coefficient. A common point of two
--   lifted hemispheres at height `h > 0` forces `f₁(s) = f₂(s) = h²`, so `s` lies in the zero
--   set of the affine function `f₁ − f₂`. Affineness is what makes the remaining geometry a
--   finite case split instead of a transcendental one.
--
--   **Verification.** The identity was checked numerically with exact rational arithmetic on
--   the Hopf-link control configuration (unit circles at the origin in the plane `z = 0`
--   and at `(0,1,0)` in the plane `x = 0`), confirming `f₁ − f₂` is constant there, which is
--   the degenerate slope-zero case.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.disk_cut_difference_affine (a e c₁ c₂ : Space3) (r₁ r₂ : ℝ) (he : (∑ i, e i * e i) = 1) (s : ℝ) : (r₁ ^ 2 - (∑ i, (a i + s * e i - c₁ i) * (a i + s * e i - c₁ i))) - (r₂ ^ 2 - (∑ i, (a i + s * e i - c₂ i) * (a i + s * e i - c₂ i))) = (r₁ ^ 2 - r₂ ^ 2) - (∑ i, (a i - c₁ i) * (a i - c₁ i)) + (∑ i, (a i - c₂ i) * (a i - c₂ i)) - 2 * s * ((∑ i, e i * (a i - c₁ i)) - (∑ i, e i * (a i - c₂ i))) := by sorry
