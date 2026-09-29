-- Prove2me | Theorems.Thm_mapsTo_rectangleBorder_left_re
-- name    : mapsTo_rectangleBorder_left_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:04:23.36972+00:00
-- url     : https://prove2.me/theorems/58a6d1e7-fb5d-479c-b33d-a2cad2193a8d
-- title:
--   The vertical segment at abscissa $\operatorname{Re} z$ lies on the rectangle border
-- statement:
--   Let $z, w \in \mathbb{C}$ be two corners determining an axis-parallel rectangle, and let $[[\operatorname{Im} z, \operatorname{Im} w]]$ denote the unordered closed interval between $\operatorname{Im} z$ and $\operatorname{Im} w$. Then the vertical parametrization at real part $\operatorname{Re} z$,
--
--   $$y \;\longmapsto\; \operatorname{Re} z + i y, \qquad y \in [[\operatorname{Im} z, \operatorname{Im} w]],$$
--
--   maps into the border of the rectangle with corners $z$ and $w$.
--
--   This inclusion lemma handles the left vertical edge of a rectangle contour: it shows the standard parametrization of that edge by its imaginary part remains on the rectangle boundary, so that conditions imposed on the border (holomorphy of an integrand, pointwise bounds) apply along the corresponding vertical line integral in the rectangle version of Cauchy's theorem and the residue computations built on it.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Rectangle.lean#L189-L192

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Definitions.Def_Rectangle_defs

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

open Rectangle

theorem mapsTo_rectangleBorder_left_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑z.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) := by sorry
