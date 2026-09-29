-- Prove2me | Theorems.Thm_Zeta23_Tail_TailHyp_summable_Gsummand
-- name    : Zeta23.Tail.TailHyp.summable_Gsummand
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:45:45.401605+00:00
-- url     : https://prove2.me/theorems/7df4e9e3-4c2d-4301-9ffd-201624995ff2
-- title:
--   Entrywise summability of the zero-side series defining $G$
-- statement:
--   **Setup.** Work under a tail hypothesis package `TailHyp Z P T A₀ C₁` (local zero count with constant $A_0 \ge 1$, decay bound [eq:hfbound] for $\hat\varphi$ with constant $e^{L/4}C_1$, $T \ge 300$, $L \ge 2$). For grid indices $k, l < d$ the summand `Z.Gsummand P T k l ρ` is
--   $$m_\rho\, \hat\varphi(\gamma_\rho - \tau_k)\, \hat\varphi(\gamma_\rho - \tau_l),$$
--   where $m_\rho$ is the multiplicity of the zero $\rho$, $\gamma_\rho = \operatorname{Im}\rho$, $\tau_k = T + k\cdot 2\pi/L$ are the grid points, and $\hat\varphi$ is the (paper-normalized) Fourier transform of the taper $\varphi$.
--
--   **Statement.** For every pair of grid indices $k, l \in \{0,\dots,d-1\}$, the family
--   $$\rho \;\longmapsto\; m_\rho\, \hat\varphi(\gamma_\rho - \tau_k)\, \hat\varphi(\gamma_\rho - \tau_l)$$
--   is summable over *all* distinct zeros $\rho$ in the configuration $Z$ (in the sense of Lean's unconditional `Summable`, i.e. absolute/net convergence).
--
--   This establishes the absolute convergence of the first expression in [eq:Gdef] — here *derived* from the entry decay [eq:hfbound] and the local zero count, rather than assumed.
--
--   **Role.** It feeds `TailHyp.hasSum_Ez` in `Zeta23.Tail`: once each entry series converges, the tail matrix $E = G - A$ can be written as a convergent sum of rank-one contributions from the tail zeros, which underlies the operator-norm and trace-norm bounds of Proposition [prop:tail].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Tail.lean#L362-L378, docstring tags [eq:Gdef], [eq:hfbound]

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

theorem Zeta23.Tail.TailHyp.summable_Gsummand (k l : Fin (P.d T)) :
    Summable (fun ρ : Z.carrier => Z.Gsummand P T k l ρ) := by sorry
