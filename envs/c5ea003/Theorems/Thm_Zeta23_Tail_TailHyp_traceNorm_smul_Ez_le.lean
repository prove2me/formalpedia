-- Prove2me | Theorems.Thm_Zeta23_Tail_TailHyp_traceNorm_smul_Ez_le
-- name    : Zeta23.Tail.TailHyp.traceNorm_smul_Ez_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:46:24.324425+00:00
-- url     : https://prove2.me/theorems/c1df5e2b-594c-4337-b60e-fa4c229f4979
-- title:
--   Trace norm of the scaled tail matrix: $\|\kappa\, E\|_1 \le \kappa\, L\,\theta_0$
-- statement:
--   **Setup.** Under a tail hypothesis package `TailHyp Z P T A₀ C₁`, let $E = $ `Z.Ez P T` $= G - A$ be the zero-side tail matrix of [eq:AE] — the contribution to the $d\times d$ matrix $G$ of the zeros with ordinate outside the window $I' = (T-\sqrt T, 2T+\sqrt T]$. For a Hermitian matrix, `traceNorm` is defined as $\sum_i |\lambda_i|$, the sum of the absolute values of its eigenvalues. Write $\theta_0 = 4A_0K^2\log(4T)/T$ with $K = e^{L/4}C_1$, and $L = P.L\,T$.
--
--   **Statement.** For every real scalar $\kappa \ge 0$ such that the scaled matrix $\kappa \cdot E$ is Hermitian (hypothesis `hM`),
--   $$\|\kappa\, E\|_1 \;\le\; \kappa \cdot \bigl(L\cdot\theta_0(A_0,\, e^{L/4}C_1,\, T)\bigr).$$
--   The proof route is the rank-one decomposition $\kappa\,E = \sum_\rho (\kappa\, m_\rho)\, u_\rho u_\rho^{\mathsf T}$ over tail zeros together with `traceNorm_le_of_hasSum_vecMulVec` and the partial-sum bound $\sum m_\rho\|u_\rho\|_2^2 \le L\theta_0$.
--
--   **Role.** Applied with $\kappa = 1/L$ and $\kappa = 1/(aL^2)$ it produces the two bounds of Proposition [prop:tail] (`prop_tail` in `Zeta23.Tail`): $\|\tilde E\|_1 \le \theta_0$ and $\|\hat E\|_1 \le \theta_0/(aL)$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail.lean#L422-L436

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_Tail
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne

open Matrix Finset Complex
open scoped ComplexOrder
open Zeta23
open Tail
open RHLinalg
variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}
open TailHyp
variable (H : TailHyp Z P T A₀ C₁)
include H

theorem Zeta23.Tail.TailHyp.traceNorm_smul_Ez_le {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : (((κ : ℝ) : ℂ) • Z.Ez P T).IsHermitian) :
    traceNorm hM ≤ κ * (P.L T * theta0 A₀ H.K T) := by sorry
