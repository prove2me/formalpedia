-- Prove2me | Theorems.Thm_Zeta23_Assembly_eventually_clam_bounds
-- name    : Zeta23.Assembly.eventually_clam_bounds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:41:45.08863+00:00
-- url     : https://prove2.me/theorems/5c980b29-a1f1-4386-bb29-0df2d64349dd
-- title:
--   Eventual bounds for $c_\lambda = 1/\lambda_1 + \lambda_1/3$
-- statement:
--   For a fixed parameter pack $P$ with exponent $\lambda = $ `P.lam`, write $l = \log(T/2\pi)$, $L = \lambda l$, $\ell_1 = l + 2\log 2 - 1$, and $\lambda_1 = \lambda_1(T) := L/\ell_1$. Assume $0 < \lambda \le 1$.
--
--   The theorem asserts that for all sufficiently large $T$, the quantity $c_\lambda := 1/\lambda_1 + \lambda_1/3$ satisfies
--   $$0 \;\le\; \frac{1}{\lambda_1(T)} + \frac{\lambda_1(T)}{3} \;\le\; \frac{2}{\lambda} + \frac{1}{3}.$$
--
--   The point is that once $l \ge c_0 := 2\log 2 - 1$ one has $\lambda/2 \le \lambda_1 \le \lambda \le 1$, giving $1/\lambda_1 \le 2/\lambda$ and $\lambda_1/3 \le 1/3$. In the assembly of Theorem A, $c_\lambda$ is the coefficient of $N$ in the Frobenius-norm bound $\lVert \hat G \rVert_F^2 \lesssim c_\lambda N$, and this uniform bound (the hypothesis $c_\lambda \in [0, K]$ of `err_isLittleO`) is what keeps the error term $B\sqrt{c_\lambda N + R_2}$ of size $o(N)$. Consumed by `thmA_abstract_err`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Assembly.lean#L844-L857

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
open Filter Asymptotics Topology Real

theorem Zeta23.Assembly.eventually_clam_bounds (P : Params) (hlam : 0 < P.lam) (hlam1 : P.lam ≤ 1) :
    ∀ᶠ T in atTop, 0 ≤ 1 / P.lam1 T + P.lam1 T / 3 ∧ 1 / P.lam1 T + P.lam1 T / 3 ≤ 2 / P.lam + 1 / 3 := by sorry
