-- Prove2me | Theorems.Thm_mapsTo_rectangleBorder_left_im
-- name    : mapsTo_rectangleBorder_left_im
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:04:12.031068+00:00
-- url     : https://prove2.me/theorems/a0f4f83a-185e-4790-8705-a6a7e3d109e7
-- title:
--   The horizontal segment at height $\operatorname{Im} z$ lies on the rectangle border
-- statement:
--   Let $z, w \in \mathbb{C}$ be two corners determining an axis-parallel rectangle, and let $[[\operatorname{Re} z, \operatorname{Re} w]]$ denote the unordered closed interval between $\operatorname{Re} z$ and $\operatorname{Re} w$. Then the horizontal parametrization at height $\operatorname{Im} z$,
--
--   $$x \;\longmapsto\; x + i \operatorname{Im} z, \qquad x \in [[\operatorname{Re} z, \operatorname{Re} w]],$$
--
--   maps into the border of the rectangle with corners $z$ and $w$ (the union of its four edges).
--
--   This is one of the four side-inclusion lemmas for rectangle contours: it certifies that the natural real-interval parametrization of the bottom (respectively top, depending on orientation) horizontal edge stays on the rectangle boundary. Such lemmas let hypotheses stated on the rectangle border (e.g. holomorphy or bounds on an integrand along the contour) be transported to the four one-dimensional integrals that make up a rectangle contour integral.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Rectangle.lean#L199-L202

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Definitions.Def_Rectangle_defs

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

open Rectangle

theorem mapsTo_rectangleBorder_left_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + z.im * I) [[z.re, w.re]] (RectangleBorder z w) := by sorry
