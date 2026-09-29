-- Prove2me | Theorems.Thm_Zeta23_Tail_TailHyp_Ez_isHermitian
-- name    : Zeta23.Tail.TailHyp.Ez_isHermitian
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:45:57.081657+00:00
-- url     : https://prove2.me/theorems/2bc2804a-f5da-4f7e-89f2-340bbca25354
-- title:
--   The tail matrix $E = G - A$ is Hermitian
-- statement:
--   Setting: $Z$ is a `ZeroConfig` (invariant under the reflection $\rho \mapsto 1 - \bar\rho$ with equal multiplicities), $P$ a parameter pack with taper transform $\widehat\varphi = P.\mathrm{phiHat}$, and $H : \mathrm{TailHyp}\ Z\ P\ T\ A_0\ C_1$ the standing hypotheses of the tail proposition ($T \ge T_0$, $L \ge 2$, local zero count, decay bound [eq:hfbound]). The matrix $E := G - A$ (`Z.Ez P T`) is the tail part of the zero-side Gram matrix: the contribution of the zeros with ordinate outside $I' = (T - \sqrt T,\, 2T + \sqrt T]$, including all zeros with $\gamma \le 0$.
--
--   **Statement.** If moreover $\widehat\varphi$ commutes with conjugation, $\widehat\varphi(\bar z) = \overline{\widehat\varphi(z)}$ for all $z \in \mathbb{C}$, then $E$ is a Hermitian matrix: $E^{\mathsf H} = E$.
--
--   The proof pairs each tail zero $\rho$ with its reflection $1 - \bar\rho$ (also a tail zero, with $m_{1-\bar\rho} = m_\rho$ and $u_{1-\bar\rho} = \bar u_\rho$) in the rank-one series $E = \sum_{\gamma \notin I'} m_\rho\, u_\rho u_\rho^{\mathsf T}$ furnished by `hasSum_Ez`.
--
--   Hermitian-ness is what makes the spectral bounds (Weyl eigenvalue comparison, trace-norm estimates) of the matrix-variational argument applicable to $E$; the theorem is consumed by `Zeta23.Tail.eventually_tailInputs`, which packages [prop:tail] for the assembly.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail.lean#L507-L542

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
variable {P : Params} {T : ℝ}
variable {Z : ZeroConfig} {A₀ C₁ : ℝ}

theorem Zeta23.Tail.TailHyp.Ez_isHermitian (H : TailHyp Z P T A₀ C₁)
    (hconj : ∀ z : ℂ, P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    (Z.Ez P T).IsHermitian := by sorry
