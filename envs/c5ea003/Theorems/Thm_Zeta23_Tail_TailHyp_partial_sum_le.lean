-- Prove2me | Theorems.Thm_Zeta23_Tail_TailHyp_partial_sum_le
-- name    : Zeta23.Tail.TailHyp.partial_sum_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:45:38.787955+00:00
-- url     : https://prove2.me/theorems/72333869-0176-4fab-b76f-e67e3286fb3d
-- title:
--   Finite partial sums over tail zeros: $\sum m_\rho \|u_\rho\|_2^2 \le L\,\theta_0$
-- statement:
--   **Setup.** Fix an abstract zero configuration $Z$ (a set of nontrivial zeros $\rho$ with multiplicities $m_\rho = $ `Z.mult ρ` and ordinates $\gamma_\rho = \operatorname{Im}\rho$), parameters $P$ and a height $T$, together with a tail hypothesis package `TailHyp Z P T A₀ C₁`. This bundle records: $T \ge T_0 := 300$, $L \ge 2$ (where $L = P.L\,T = \lambda\,\ell(T)$, $\ell(T) = \log(T/2\pi)$), $A_0 \ge 1$ with the unit-window local zero count $N(t,t+1] \le A_0\log(|t|+3)$ for all real $t$, and the decay bound [eq:hfbound] for the taper transform: $\|\hat\varphi(r-iy)\| \le e^{L/4}C_1/\|r-iy\|^2$ for $|y|\le 1/2$. For each zero $\rho$ the vector $u_\rho \in \mathbb{C}^d$ has entries $u_\rho(k) = \hat\varphi(\gamma_\rho - \tau_k)$, where $\tau_k = T + k\cdot 2\pi/L$ are the grid points and $d = \lfloor LT/2\pi \rfloor$. The tail consists of the zeros outside the enlarged window $I' = (T-\sqrt T,\, 2T+\sqrt T]$ (the complement of the finite set `H.sA`), and $\theta_0 = \theta_0(A_0, K, T) := 4A_0K^2\log(4T)/T$ with $K := e^{L/4}C_1$.
--
--   **Statement.** For every *finite* set $u$ of tail zeros,
--   $$\sum_{\rho \in u} m_\rho \sum_{k<d} \|u_\rho(k)\|^2 \;\le\; L\cdot \theta_0\!\left(A_0,\, e^{L/4}C_1,\, T\right).$$
--   This is the finite-partial-sum form of the paper's estimate "[eq:Enormsum] gives $\|E\| \le 4A_0C_1^2X^{1/2}L\log(4T)D_0^{-2} = L\theta_0$"; stating it for finite subfamilies avoids presupposing any summability.
--
--   **Role.** This is the quantitative heart of the tail bound in `Zeta23.Tail`: it feeds `summable_Gsummand` (absolute convergence of the zero-side matrix entries) and `traceNorm_smul_Ez_le` (the trace-norm bound on the tail matrix $E$), on the way to Proposition [prop:tail].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail.lean#L313-L347, docstring tag [eq:Enormsum]

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

theorem Zeta23.Tail.TailHyp.partial_sum_le (u : Finset {ρ : Z.carrier // ρ ∉ H.sA}) :
    ∑ x ∈ u, (Z.mult (x : Z.carrier) : ℝ) * ∑ k, ‖uvec P T (x : Z.carrier) k‖ ^ 2
      ≤ P.L T * theta0 A₀ H.K T := by sorry
