-- Prove2me | Theorems.Thm_Zeta23_Assembly_frobGhat_le
-- name    : Zeta23.Assembly.frobGhat_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:41:57.227314+00:00
-- url     : https://prove2.me/theorems/56bc2036-275b-44b6-8dba-a01495c1c0bf
-- title:
--   Explicit form of $\lVert\hat{G}\rVert_F^2 \le c_\lambda N (1 + O(\mathcal{E}'_T))$
-- statement:
--   A scalar inequality making explicit the paper's bound $\lVert\hat G\rVert_F^2 \le (1/\lambda_1 + \lambda_1/3)\, N\, (1 + O(\mathcal{E}'_T))$. All quantities are real numbers: $a, L, T, \ell_1 > 0$ are the taper normalization, mollifier length, height, and shifted log-height; $\mathrm{tr}\,\tilde G^2$ (`trG2`) is the second trace; $C \mathcal{E}$ the relative error of [eq:tr2]; $N$ the zero count and $R_N$ its Riemann–von Mangoldt remainder.
--
--   Assume $1 + C\mathcal{E} \ge 0$, the upper half of [eq:tr2] in the form
--   $$\mathrm{tr}\,\tilde G^2 - \frac{TL}{2\pi}\left(\ell_1^2 + \frac{L^2}{3}\right) \le C\mathcal{E}\cdot\frac{TL}{2\pi}\left(\ell_1^2 + \frac{L^2}{3}\right),$$
--   and Riemann–von Mangoldt in the form $T\ell_1/(2\pi) \le N + R_N$ ([eq:RvM]). Then, with $\lambda_1 := L/\ell_1$, $c_\lambda := 1/\lambda_1 + \lambda_1/3$, and $K := (1 + C\mathcal{E})/a^2$,
--   $$\frac{\mathrm{tr}\,\tilde G^2}{(aL)^2} \;\le\; c_\lambda N + c_\lambda\Big((K - 1)N + K R_N\Big).$$
--
--   The left side equals $\lVert\hat G\rVert_F^2$ in hat units, and the second summand is the explicit remainder $R_2$ fed into `err_isLittleO`. Consumed by `thmA_abstract_err` in the assembly of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Assembly.lean#L444-L475, docstring tags [eq:tr2], [eq:RvM]

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

theorem Zeta23.Assembly.frobGhat_le {a L T ℓ₁ trG2 C calE N RN : ℝ} (ha : 0 < a) (hL : 0 < L) (hℓ₁ : 0 < ℓ₁)
    (hK : 0 ≤ 1 + C * calE)
    (htr2 : trG2 - T * L / (2 * Real.pi) * (ℓ₁ ^ 2 + L ^ 2 / 3)
              ≤ C * calE * (T * L / (2 * Real.pi) * (ℓ₁ ^ 2 + L ^ 2 / 3)))
    (hRvM : T * ℓ₁ / (2 * Real.pi) ≤ N + RN) :
    ((a * L)⁻¹) ^ 2 * trG2
      ≤ (1 / (L / ℓ₁) + (L / ℓ₁) / 3) * N
        + (1 / (L / ℓ₁) + (L / ℓ₁) / 3) * (((1 + C * calE) / a ^ 2 - 1) * N
            + (1 + C * calE) / a ^ 2 * RN) := by sorry
