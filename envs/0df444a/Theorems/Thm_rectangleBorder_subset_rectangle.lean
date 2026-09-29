-- Prove2me | Theorems.Thm_rectangleBorder_subset_rectangle
-- name    : rectangleBorder_subset_rectangle
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:05:23.251418+00:00
-- url     : https://prove2.me/theorems/91193dcb-4317-4755-8591-5985b7c247a1
-- title:
--   The border of a rectangle is contained in the rectangle
-- statement:
--   Let $z, w \in \mathbb{C}$ and let $R(z,w)$ denote the closed axis-parallel rectangle with corners $z$ and $w$ (the product of the closed real intervals between $z_{\mathrm{re}}, w_{\mathrm{re}}$ and between $z_{\mathrm{im}}, w_{\mathrm{im}}$, viewed inside $\mathbb{C}$). Let $\partial R(z,w)$ be its border, the union of the four closed edges. Then
--
--   $$\partial R(z,w) \;\subseteq\; R(z,w).$$
--
--   That is, every point of any of the four edges belongs to the closed rectangle itself.
--
--   This containment is a basic sanity lemma in the PNT+ rectangle framework for contour integration: hypotheses such as "$f$ is continuous on the rectangle" or "$f$ is holomorphic on the rectangle minus an interior point" automatically transfer to the contour $\partial R$, which is where the rectangle integral is actually evaluated.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Rectangle.lean#L123-L129

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Definitions.Def_Rectangle_defs

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

open Rectangle

theorem rectangleBorder_subset_rectangle (z w : ℂ) : RectangleBorder z w ⊆ Rectangle z w := by sorry
