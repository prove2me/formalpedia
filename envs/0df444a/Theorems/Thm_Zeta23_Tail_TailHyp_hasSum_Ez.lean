-- Prove2me | Theorems.Thm_Zeta23_Tail_TailHyp_hasSum_Ez
-- name    : Zeta23.Tail.TailHyp.hasSum_Ez
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:45:51.708537+00:00
-- url     : https://prove2.me/theorems/11b83d60-a0fb-4926-8171-f650d8c1d502
-- title:
--   $E = \sum_{\gamma \notin I'} m_\rho\, u_\rho u_\rho^{\mathsf T}$: the tail matrix as a convergent rank-one series
-- statement:
--   Setting: $Z$ is a `ZeroConfig`, $P$ a parameter pack with taper transform $\widehat\varphi$, grid $\tau_k = T + k\cdot\frac{2\pi}{L}$ ($k < d$), and $H : \mathrm{TailHyp}\ Z\ P\ T\ A_0\ C_1$ the standing hypotheses (in particular the local count and the decay $\|\widehat\varphi(r - iy)\| \le e^{L/4}C_1\,\|r - iy\|^{-2}$ of [eq:hfbound]). For a zero $\rho$, its test vector is
--   $$u_\rho \;=\; \bigl(\widehat\varphi(\gamma_\rho - \tau_k)\bigr)_{0 \le k < d} \in \mathbb{C}^{d},$$
--   and $u_\rho u_\rho^{\mathsf T}$ denotes the outer product **without conjugation** (`vecMulVec`). $H.sA$ is the finite set of zeros with ordinate in the window $I' = (T-\sqrt T,\, 2T+\sqrt T]$, so the index set $\{\rho \in Z.\mathrm{carrier} : \rho \notin H.sA\}$ is exactly the tail zeros ($\gamma \notin I'$, including all $\gamma \le 0$).
--
--   **Statement.** The family of rank-one matrices $\rho \mapsto m_\rho \cdot u_\rho u_\rho^{\mathsf T}$, indexed by the tail zeros, has sum (in the sense of `HasSum`, i.e. unconditional convergence of the net of finite partial sums, entrywise) equal to the matrix $E := G - A$ (`Z.Ez P T`) of [eq:AE]:
--   $$E \;=\; \sum_{\gamma_\rho \notin I'} m_\rho\, u_\rho u_\rho^{\mathsf T}.$$
--
--   Convergence comes from the $\widehat\varphi$ decay and the local zero count rather than being assumed. This series representation is the engine of the tail proposition [prop:tail]: it is consumed by `Zeta23.Tail.TailHyp.Ez_isHermitian` (Hermitian symmetry via $\rho \mapsto 1-\bar\rho$) and by `Zeta23.Tail.TailHyp.traceNorm_smul_Ez_le` (the trace-norm bound $\|\widehat E\|_1 \le \theta_0/(aL)$).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail.lean#L404-L420, docstring tag [eq:AE]

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

theorem Zeta23.Tail.TailHyp.hasSum_Ez :
    HasSum (fun x : {ρ : Z.carrier // ρ ∉ H.sA} =>
      ((Z.mult (x : Z.carrier) : ℝ) : ℂ) • vecMulVec (uvec P T (x : Z.carrier)) (uvec P T (x : Z.carrier)))
      (Z.Ez P T) := by sorry
