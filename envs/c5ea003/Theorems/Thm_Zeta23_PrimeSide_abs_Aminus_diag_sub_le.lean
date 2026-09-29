-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_abs_Aminus_diag_sub_le
-- name    : Zeta23.PrimeSide.abs_Aminus_diag_sub_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:10:06.436308+00:00
-- url     : https://prove2.me/theorems/7818dd56-ea87-4901-b9c4-460a1c3d172a
-- title:
--   Diagonal kernel asymptotics: $\bigl|A^-(y,y) - T\!\int\Phi(x)^2\cos(xy)\,dx\bigr| \le \int\Phi(x)^2|x|\,dx$
-- statement:
--   Here $A^-(y,y') = \int_{[-T,T]}\Phi(x)^2 J^-(x)\,dx$ (`Aminus`) is the difference-frequency kernel of the $P\times P$ decomposition, where $J^-(x)$ is the inner integral over the sheared window $I \cap (I-x)$, $I = [T,2T]$. On the diagonal $y' = y$ the frequency $y - y'$ vanishes and the inner integral evaluates to $(T - |x|)\cos(xy)$.
--
--   Assume $T \ge 0$, $\Phi$ continuous, and that $\Phi^2$ and $\Phi(x)^2|x|$ are integrable. Then for every real $y$,
--   $$\Bigl|A^-(y,y) \;-\; T\int_{\mathbb R}\Phi(x)^2\cos(xy)\,dx\Bigr| \;\le\; \int_{\mathbb R}\Phi(x)^2\,|x|\,dx,$$
--   the error collecting the $-|x|\cos(xy)$ defect on $[-T,T]$ and the tail $\int_{|x|>T}\Phi^2 \le \int\Phi^2|x|/T$ (§5.4).
--
--   Via the Fourier identity [eq:Phi2FT] ($\int\Phi(x)^2\cos(xy)\,dx = 2\pi g(y)$), this turns the diagonal term $\mathcal D$ into $(T/\pi)\sum_n a_n^2\,g(y_n)$ plus an admissible error; it is consumed by `diag_estimate` in [prop:PP] (module `Zeta23.PrimeSideB.PPKernel`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PPKernel.lean#L341-L382, docstring tag [eq:Phi2FT]

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
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideB_PPKernel

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction ComplexConjugate
open Zeta23
open PrimeSide
variable {Φ : ℝ → ℝ} {T : ℝ}

theorem Zeta23.PrimeSide.abs_Aminus_diag_sub_le (hT : 0 ≤ T) (hΦ : Continuous Φ)
    (hΦ2 : Integrable fun x => Φ x ^ 2) (hΦabs : Integrable fun x => Φ x ^ 2 * |x|) (y : ℝ) :
    |Aminus Φ T y y - T * ∫ x, Φ x ^ 2 * Real.cos (x * y)| ≤ ∫ x, Φ x ^ 2 * |x| := by sorry
