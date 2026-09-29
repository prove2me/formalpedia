-- Prove2me | Theorems.Thm_PNTA_mem_Rect
-- name    : PNTA.mem_Rect
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-12T06:09:42.986379+00:00
-- url     : https://prove2.me/theorems/fe693017-d871-472d-bf36-b5fd7efd0f8b
-- title:
--   Membership criterion for an axis-parallel rectangle
-- statement:
--   An explicit coordinate description of the points of a rectangle.
--
--   Let $z$ and $w$ satisfy $\mathrm{Re}\, z \le \mathrm{Re}\, w$ and $\mathrm{Im}\, z \le \mathrm{Im}\, w$. Then a point $p$ lies in the rectangle with opposite corners $z$ and $w$ if and only if all four coordinate inequalities hold:
--   $$\mathrm{Re}\, z \le \mathrm{Re}\, p \le \mathrm{Re}\, w \quad\text{and}\quad \mathrm{Im}\, z \le \mathrm{Im}\, p \le \mathrm{Im}\, w .$$
--
--   The ordering hypotheses on the corners are what make the two coordinate intervals the expected ones. This is the workhorse for verifying that a specific point — typically a pole being enclosed — lies inside a given contour.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Rectangle.lean#L77-L82

/-
Extracted from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit f55e85551ac10e96d98262a354cfcaac2825f2da, Apache 2.0 license.
Wrapped in namespace PNTA for the Prove2Me platform.
-/

import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone

open Complex Set Topology
open scoped Interval
variable {z w : ℂ} {c : ℝ}

theorem PNTA.mem_Rect {z w : ℂ} (zRe_lt_wRe : z.re ≤ w.re) (zIm_lt_wIm : z.im ≤ w.im) (p : ℂ) :
    p ∈ Rectangle z w ↔
      z.re ≤ p.re ∧ p.re ≤ w.re ∧ z.im ≤ p.im ∧ p.im ≤ w.im := by sorry
