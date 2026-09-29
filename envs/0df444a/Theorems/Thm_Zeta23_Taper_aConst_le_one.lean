-- Prove2me | Theorems.Thm_Zeta23_Taper_aConst_le_one
-- name    : Zeta23.Taper.aConst_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:29:26.835985+00:00
-- url     : https://prove2.me/theorems/ca6df84a-944f-4e71-bc86-cd489f6a2433
-- title:
--   The normalization constant $a = L^{-1}\int \varphi^2 \le 1$
-- statement:
--   **Setup.** A taper profile $\varrho$ (`TaperProfile ϱ`) is a $C^3$, monotone function on $\mathbb{R}$ equal to $0$ on $(-\infty, 0]$ and to $1$ on $[1, \infty)$. From it, with length $L$ and ramp width $w$ satisfying $0 < w$ and $2w \le L$, the taper is defined by $\varphi(u) := \varrho\bigl((L/2 - |u|)/w\bigr)$ [eq:phidef] — a plateau function supported exactly on $[-L/2, L/2]$, with values in $[0,1]$. The constant of [eq:abdef] is
--   $$a \;=\; \texttt{aConst}\ \varrho\ L\ w \;:=\; \frac{1}{L}\int_{\mathbb{R}} \varphi(u)^{2}\, du.$$
--
--   **Statement.** Under these hypotheses,
--   $$a \;\le\; 1.$$
--   Indeed $0 \le \varphi \le 1$ and $\operatorname{supp}\varphi \subseteq [-L/2, L/2]$, so $\int \varphi^2 \le L$.
--
--   **Role.** Together with the lower bound $a \ge 1/2$ proved elsewhere, this pins the normalization $a$ of the diagonal matrix entries into $[1/2, 1]$. It is consumed by `Zeta23.PrimeSide.localHyps_concrete` (instantiating the prime-side local hypotheses for the concrete taper) and by `Zeta23.eventually_side_conditions` in the final assembly of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Taper/Norms.lean#L541-L576

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Taper_Basic

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem Zeta23.Taper.aConst_le_one (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    aConst ϱ L w ≤ 1 := by sorry
