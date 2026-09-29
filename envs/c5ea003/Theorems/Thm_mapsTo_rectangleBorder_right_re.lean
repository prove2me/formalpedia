-- Prove2me | Theorems.Thm_mapsTo_rectangleBorder_right_re
-- name    : mapsTo_rectangleBorder_right_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:04:46.409464+00:00
-- url     : https://prove2.me/theorems/9bf0ecd2-4d6c-4f13-92c8-b80e5002d20a
-- title:
--   The vertical segment at abscissa $\operatorname{Re} w$ lies on the rectangle border
-- statement:
--   Let $z, w \in \mathbb{C}$ be two corners determining an axis-parallel rectangle, and let $[[\operatorname{Im} z, \operatorname{Im} w]]$ denote the unordered closed interval between $\operatorname{Im} z$ and $\operatorname{Im} w$. Then the vertical parametrization at real part $\operatorname{Re} w$,
--
--   $$y \;\longmapsto\; \operatorname{Re} w + i y, \qquad y \in [[\operatorname{Im} z, \operatorname{Im} w]],$$
--
--   maps into the border of the rectangle with corners $z$ and $w$.
--
--   This inclusion lemma covers the right vertical edge of a rectangle contour. In the residue calculus on rectangles, hypotheses are naturally stated on the whole rectangle border, while integrals are computed edge by edge; these MapsTo lemmas are the glue that restricts border-level hypotheses to each parametrized edge.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Rectangle.lean#L194-L197

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Definitions.Def_Rectangle_defs

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

open Rectangle

theorem mapsTo_rectangleBorder_right_re (z w : ℂ) :
    MapsTo (fun (y : ℝ) => ↑w.re + ↑y * I) [[z.im, w.im]] (RectangleBorder z w) := by sorry
