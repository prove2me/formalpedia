-- Prove2me | Theorems.Thm_rectangle_mem_nhds_iff
-- name    : rectangle_mem_nhds_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:04:58.571201+00:00
-- url     : https://prove2.me/theorems/6acc033d-4619-41c3-9897-aeffeb433822
-- title:
--   A rectangle is a neighborhood of $p$ iff $p$ lies in its open interior
-- statement:
--   Let $z, w, p \in \mathbb{C}$, and let $R(z,w)$ be the closed axis-parallel rectangle with corners $z$ and $w$. Then $R(z,w)$ is a neighborhood of $p$ if and only if $p$ belongs to the open rectangle obtained from the open intervals between the coordinates:
--
--   $$R(z,w) \in \mathcal{N}(p) \;\iff\; p \in \big( \operatorname{uIoo}(z_{\mathrm{re}}, w_{\mathrm{re}}) \big) \times_{\mathbb{C}} \big( \operatorname{uIoo}(z_{\mathrm{im}}, w_{\mathrm{im}}) \big),$$
--
--   where $\operatorname{uIoo}(a,b)$ denotes the open interval with endpoints $\min(a,b)$ and $\max(a,b)$, and $\times_{\mathbb{C}}$ is the product of a real set and an imaginary set inside $\mathbb{C}$ (real part in the first factor, imaginary part in the second).
--
--   This characterization identifies the topological interior of the closed rectangle as the corresponding open box, with no orientation assumption on the corners $z, w$. It is the workhorse lemma for checking, in residue arguments on rectangles, that a prospective pole $p$ lies strictly inside the contour --- the hypothesis under which the rectangle integral picks up the residue at $p$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Rectangle.lean#L168-L171

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Definitions.Def_Rectangle_defs

open Complex Set Topology

open scoped Interval

variable {z w : ℂ} {c : ℝ}

open Rectangle

theorem rectangle_mem_nhds_iff {z w p : ℂ} :
    Rectangle z w ∈ 𝓝 p ↔ p ∈ (Set.uIoo z.re w.re) ×ℂ (Set.uIoo z.im w.im) := by sorry
