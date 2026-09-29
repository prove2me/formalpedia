-- Prove2me | Theorems.Thm_Zeta23_ZeroSide_ZeroBlockData_rtrace_onPart
-- name    : Zeta23.ZeroSide.ZeroBlockData.rtrace_onPart
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:54:25.616575+00:00
-- url     : https://prove2.me/theorems/6acc5c6f-2534-4adf-b9d7-190a9af18b7f
-- title:
--   Trace of the on-line part: $\operatorname{tr}\bigl(\sum m_z u_z u_z^{\mathsf T}\bigr) = \sum m_z \|u_z\|^2$
-- statement:
--   In the abstract zero-side data `ZeroBlockData`, the on-line part of the window matrix is
--   $$\mathrm{onPart} \;=\; \sum_{z \text{ on-line}} m_z\, u_z u_z^{\mathsf T},$$
--   where the sum runs over the points fixed by the involution $\sigma$ (i.e. the zeros with $\beta = 1/2$), $m_z$ is the multiplicity and $u_z = v(z) \in \mathbb{C}^d$ the evaluation vector; for on-line $z$ the vector $u_z$ is real (it is fixed by entrywise conjugation, since $v(\sigma z) = \overline{v(z)}$). `rtrace` denotes the real part of the trace.
--
--   **Statement.**
--   $$\operatorname{tr}(\mathrm{onPart}) \;=\; \sum_{z \text{ on-line}} m_z \sum_k \| v(z)_k \|^2.$$
--   For a real vector $u$, $\operatorname{tr}(m\, u u^{\mathsf T}) = m \sum_k u_k^2 = m \|u\|^2$; summing over the on-line points gives the identity.
--
--   **Role.** In the module `Zeta23.ZeroSide` this trace computation feeds `rtrace_blockP_le`, the bound $\operatorname{tr} P \le N_{\mathrm{on}}(I')$ of prop:block (ii).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ZeroSide.lean#L493-L507

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_ZeroSide

set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23
open Zeta23.ZeroSide
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
open ZeroBlockData
variable (D : ZeroBlockData ι d)
variable {D}
variable (D) (P : D.PairReps)

theorem Zeta23.ZeroSide.ZeroBlockData.rtrace_onPart : rtrace D.onPart = ∑ z ∈ D.onLine, (D.m z : ℝ) * ∑ k, ‖D.v z k‖ ^ 2 := by sorry
