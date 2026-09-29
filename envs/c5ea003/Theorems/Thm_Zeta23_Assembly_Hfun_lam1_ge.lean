-- Prove2me | Theorems.Thm_Zeta23_Assembly_Hfun_lam1_ge
-- name    : Zeta23.Assembly.Hfun_lam1_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:40:26.977071+00:00
-- url     : https://prove2.me/theorems/4b497c2e-475a-4f5f-a3a3-a9e25a56e558
-- title:
--   Comparison $H(\lambda_1) \ge H(\lambda) - 1/(\lambda l)$
-- statement:
--   Let $H(x) := 2 - 1/x - x/3$ be the density function of the paper, $l = l(T) := \log(T/2\pi)$, and $\ell_1 := l + 2\log 2 - 1$. For a fixed parameter pack $P$ with mollifier-length exponent $\lambda = $ `P.lam`, set $L := \lambda l$ and $\lambda_1 := L/\ell_1$ (so $\lambda_1 = \lambda + O(1/l)$, and $\lambda_1 \ne \lambda$).
--
--   Assume $\lambda > 0$ and $l(T) > 0$. Then
--   $$H(\lambda) - \frac{1}{\lambda\, l(T)} \;\le\; H(\lambda_1(T)).$$
--
--   This is the step in the paper's §6 proof of Theorem A where the variational constant naturally produced at the shifted exponent $\lambda_1$ is compared with $H(\lambda)$: since $H'(x) = x^{-2} - 1/3$ and $0 \le \lambda - \lambda_1 \le \lambda/l$, one loses at most $1/(\lambda l)$. The Lean proof uses the exact identity $H(\lambda) - H(\lambda_1) = c_0/(\lambda l) - (\lambda - \lambda_1)/3$ with $c_0 = 2\log 2 - 1 < 1$. It feeds directly into `thmA_abstract_err`, the abstract $\varepsilon$-form of Theorem A in the `Zeta23.Assembly` module.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Assembly.lean#L261-L277, docstring: the paper §6, proof of Thm A

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
open Real

theorem Zeta23.Assembly.Hfun_lam1_ge (P : Params) (T : ℝ) (hlam : 0 < P.lam) (hl : 0 < l T) :
    Hfun P.lam - 1 / (P.lam * l T) ≤ Hfun (P.lam1 T) := by sorry
