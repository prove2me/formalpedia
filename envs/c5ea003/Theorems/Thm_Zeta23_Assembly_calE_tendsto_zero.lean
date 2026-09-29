-- Prove2me | Theorems.Thm_Zeta23_Assembly_calE_tendsto_zero
-- name    : Zeta23.Assembly.calE_tendsto_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:40:48.75346+00:00
-- url     : https://prove2.me/theorems/5e46430e-880e-497d-8b14-b8707bc76da4
-- title:
--   The error rate $\mathcal{E}_T$ tends to $0$
-- statement:
--   For a fixed parameter pack $P$ with exponent $\lambda = $ `P.lam` and ramp width $w = $ `P.w`, write $l = \log(T/2\pi)$, $L = \lambda l$, $X = e^L = (T/2\pi)^\lambda$, and let $\mathcal{E}_T$ be the error rate of [thm:traces]:
--   $$\mathcal{E}_T \;:=\; \frac{w}{L} + \frac{(l^2 + X)\log l}{T\, l} + T^{\lambda/2 - 1}.$$
--
--   The theorem asserts that if $0 < \lambda \le 1$ and $w \ge 0$, then $\mathcal{E}_T \to 0$ as $T \to \infty$. The proof goes through the intermediate bound $\mathcal{E}_T \le w/L + (\log T)^2/T + \log l / l + T^{\lambda/2-1}$ valid for $T \ge 2\pi$, $l \ge 1$ (note $X \le T/2\pi$ when $\lambda \le 1$).
--
--   $\mathcal{E}_T$ is the common relative error in all four trace asymptotics of [thm:traces] (the mollified second-moment computation on the prime side), so this limit is exactly what makes those asymptotics genuinely asymptotic. It is consumed by `Zeta23.eventually_side_conditions` when the abstract Theorem A machinery is instantiated.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Assembly.lean#L1577-L1626, docstring tag [thm:traces]

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Assembly
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_PrimeSideTemp
import Definitions.Def_Zeta23_TracesBoundsE

open Matrix Finset RHLinalg
open scoped ComplexOrder
open Zeta23
open Assembly
open Filter Topology Real

theorem Zeta23.Assembly.calE_tendsto_zero (P : Params) (hlam : 0 < P.lam) (hlam1 : P.lam ≤ 1) (hw : 0 ≤ P.w) :
    Tendsto P.calE atTop (𝓝 0) := by sorry
