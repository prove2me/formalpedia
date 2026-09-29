-- Prove2me | Theorems.Thm_not_mem_rectangleBorder_of_rectangle_mem_nhds
-- name    : not_mem_rectangleBorder_of_rectangle_mem_nhds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:05:11.113917+00:00
-- url     : https://prove2.me/theorems/d2ce0450-2d8e-4253-9421-c254e63992cd
-- title:
--   A point interior to a rectangle does not lie on the rectangle's border
-- statement:
--   Let $z, w \in \mathbb{C}$ and consider the closed axis-parallel rectangle $R(z,w) = [z_{\mathrm{re}}, w_{\mathrm{re}}] \times [z_{\mathrm{im}}, w_{\mathrm{im}}]$ (as a subset of $\mathbb{C}$, with sides taken as unordered intervals), together with its border $\partial R(z,w)$, the union of its four edges. Suppose $p \in \mathbb{C}$ is a point such that $R(z,w)$ is a neighborhood of $p$, i.e. $R(z,w) \in \mathcal{N}(p)$. Then
--
--   $$p \notin \partial R(z,w).$$
--
--   In other words, if the rectangle contains an open set around $p$, then $p$ must lie in the interior and cannot be on any of the four boundary edges.
--
--   This lemma is part of the PNT+ rectangle toolkit underlying contour integration on rectangles: residue-type arguments require the pole to sit strictly inside the contour, and this statement converts the topological hypothesis "the rectangle is a neighborhood of $p$" into the combinatorial fact that $p$ avoids the boundary, so that the integrand is well-behaved on the contour itself.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Rectangle.lean#L233-L239

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Definitions.Def_Rectangle_defs

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

open Rectangle

theorem not_mem_rectangleBorder_of_rectangle_mem_nhds {z w p : ℂ}
    (hp : Rectangle z w ∈ 𝓝 p) :
    p ∉ RectangleBorder z w := by sorry
