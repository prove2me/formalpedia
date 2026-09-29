-- Prove2me | Theorems.Thm_mapsTo_rectangleBorder_right_im
-- name    : mapsTo_rectangleBorder_right_im
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:04:34.941193+00:00
-- url     : https://prove2.me/theorems/bdfa1c6e-a4b2-415b-b3ee-ad508baa4e5e
-- title:
--   The horizontal segment at height $\operatorname{Im} w$ lies on the rectangle border
-- statement:
--   Let $z, w \in \mathbb{C}$ be two corners determining an axis-parallel rectangle, and let $[[\operatorname{Re} z, \operatorname{Re} w]]$ denote the unordered closed interval between $\operatorname{Re} z$ and $\operatorname{Re} w$. Then the horizontal parametrization at height $\operatorname{Im} w$,
--
--   $$x \;\longmapsto\; x + i \operatorname{Im} w, \qquad x \in [[\operatorname{Re} z, \operatorname{Re} w]],$$
--
--   maps into the border of the rectangle with corners $z$ and $w$.
--
--   This is the companion of the height-$\operatorname{Im} z$ lemma, covering the opposite horizontal edge of the rectangle. Together the four side-inclusion lemmas decompose the rectangle border into its parametrized edges, which is the combinatorial backbone of the rectangle contour-integration framework used for Perron-type inversion in the Prime Number Theorem project.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Rectangle.lean#L204-L207

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Definitions.Def_Rectangle_defs

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

open Rectangle

theorem mapsTo_rectangleBorder_right_im (z w : ℂ) :
    MapsTo (fun (x : ℝ) => ↑x + w.im * I) [[z.re, w.re]] (RectangleBorder z w) := by sorry
