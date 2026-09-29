-- Prove2me | Theorems.Thm_Zeta23_Tail_TailHyp_Az_eq_sum
-- name    : Zeta23.Tail.TailHyp.Az_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:44:40.182165+00:00
-- url     : https://prove2.me/theorems/a3de7210-4a31-4f59-986c-d94c280507b6
-- title:
--   $A_{kl}$ as the finite sum over the zeros of $\mathcal{Z}(I')$
-- statement:
--   Setting: $Z$ is a `ZeroConfig`, $P$ a parameter pack (`Params`: taper $\varphi$ with Fourier transform $\widehat\varphi = P.\mathrm{phiHat}$, bandwidth $L$, grid points $\tau_k = T + k\cdot\frac{2\pi}{L}$ for $k < d = \lfloor LT/2\pi\rfloor$), and $H$ a `TailHyp` bundle of standing hypotheses ($T \ge T_0$, $L \ge 2$, the local count with constant $A_0 \ge 1$, and the decay bound [eq:hfbound] for $\widehat\varphi$ with constant $C_1 \ge 0$). The zero-side summand is
--   $$G_{kl}(\rho) \;=\; m_\rho\, \widehat\varphi(\gamma_\rho - \tau_k)\, \widehat\varphi(\gamma_\rho - \tau_l),$$
--   with $\gamma_\rho$ the (complexified) ordinate of $\rho$. The matrix $A$ (`Z.Az P T`) is defined as the finite sum (`finsum`) of $G_{kl}$ over the window $\mathcal{Z}(I')$, the distinct zeros with ordinate in $I' = (T - \sqrt T,\, 2T + \sqrt T]$; and $H.sA$ is that same window realized as a `Finset` of the carrier subtype (finite by local finiteness of $Z$).
--
--   **Statement.** For all indices $k, l < d$,
--   $$A_{kl} \;=\; \sum_{x \in H.sA} G_{kl}(x),$$
--   i.e. the `finsum` defining $A$ [eq:AE] coincides with the honest finite sum over the Finset of window zeros.
--
--   This bookkeeping identity lets $E = G - A$ be identified with the series over the tail zeros: its sole consumer is `Zeta23.Tail.TailHyp.hasSum_Ez`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail.lean#L380-L402, docstring tag [eq:AE]

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

theorem Zeta23.Tail.TailHyp.Az_eq_sum (k l : Fin (P.d T)) :
    Z.Az P T k l = ∑ x ∈ H.sA, Z.Gsummand P T k l (x : ℂ) := by sorry
