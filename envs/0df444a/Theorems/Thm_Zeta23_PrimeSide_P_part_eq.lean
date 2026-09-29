-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_P_part_eq
-- name    : Zeta23.PrimeSide.P_part_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:06:13.759554+00:00
-- url     : https://prove2.me/theorems/814cdf8a-66a1-48f7-b094-1cf452f9546a
-- title:
--   $P$-part of a diagonal entry: $\int\hat\varphi(r)^2 P_X(t{+}r)\,dr = -2\sum_n a_n A_\varphi(y_n)\cos(t y_n)$
-- statement:
--   Let $p$ be a parameter setting with prime cutoff $X$, and $F$ a taper datum satisfying the window-generic package `LocalHypsCore`; in particular the Fourier identity $\int\hat\varphi(r)^2\cos(ry)\,dr = 2\pi A_\varphi(y)$ holds, where $A_\varphi = \varphi\star\varphi$. Write $a_n = \Lambda(n)/\sqrt n$ and $y_n = \log n$, and recall $P_X(\tau) = -\tfrac1\pi\sum_{n\le X}a_n\cos(\tau y_n)$ [eq:Pdef].
--
--   Then for every real $t$,
--   $$\int_{\mathbb R}\hat\varphi(r)^2\,P_X(t+r)\,dr \;=\; -2\sum_{n \le X} a_n\,A_\varphi(y_n)\,\cos(t\,y_n),$$
--   the sum over integers $0 < n \le \lfloor X\rfloor$: expanding $\cos((t+r)y_n)$ by the addition formula, the sine integral vanishes by evenness and the cosine integral is $2\pi A_\varphi(y_n)$.
--
--   At $t = \tau_k$ this identifies the $P$-part $G^P_{kk}$ of a diagonal Gram entry in [prop:trace] (§5.2); it is consumed by `sum_P_part_bound` in the trace asymptotics.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Basic.lean#L1139-L1155, docstring tag [prop:trace]

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
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem Zeta23.PrimeSide.P_part_eq (hF : LocalHypsCore cϱ p F) (t : ℝ) :
    ∫ r, F.phiHat r ^ 2 * Zeta23.PX p.X (t + r)
      = -2 * ∑ n ∈ primeRange p.X, acoef n * F.Aphi (ycoef n) * Real.cos (t * ycoef n) := by sorry
