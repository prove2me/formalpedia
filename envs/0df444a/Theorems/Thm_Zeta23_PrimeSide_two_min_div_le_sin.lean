-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_two_min_div_le_sin
-- name    : Zeta23.PrimeSide.two_min_div_le_sin
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:59:31.987489+00:00
-- url     : https://prove2.me/theorems/f3fceffc-584d-4db5-91c5-b8421436cc66
-- title:
--   Jordan's inequality on $[0, L]$: $\sin(\pi y/L) \ge 2\min(y, L-y)/L$
-- statement:
--   **Statement.** Let $L > 0$ and let $y$ be a real number with $0 \le y \le L$. Then
--
--   $$\frac{2\min(y,\, L - y)}{L} \;\le\; \sin\!\Bigl(\frac{\pi y}{L}\Bigr).$$
--
--   Equivalently (as used in §5.2 of the paper), wherever the left side is positive, $|\sin(\pi y/L)|^{-1} \le L / (2\min(y, L - y))$. This is Jordan's inequality $\sin x \ge 2x/\pi$ on $[0, \pi/2]$, symmetrized about the midpoint of $[0, \pi]$ and rescaled to $[0, L]$.
--
--   **Role.** An elementary estimate from `Zeta23.PrimeSideA.Basic` (§5.2, the prime-side off-diagonal bounds): it is used in `Zeta23.PrimeSide.Aphi_mul_sum_cos_le` to control cosecant-type sums over the grid points $\tau_k$, which enter the bounds on the off-diagonal entries of the prime-side matrix $G$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L796-L814, docstring tag §5.2

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide

theorem Zeta23.PrimeSide.two_min_div_le_sin {y L : ℝ} (hL : 0 < L) (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    2 * min y (L - y) / L ≤ Real.sin (π * y / L) := by sorry
