-- Prove2me | Theorems.Thm_Zeta23_ZeroSide_ZeroBlockData_posIndex_blockQ_le
-- name    : Zeta23.ZeroSide.ZeroBlockData.posIndex_blockQ_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:54:19.031318+00:00
-- url     : https://prove2.me/theorems/4f2d1fa0-fa99-4254-9b9a-98456295c7c5
-- title:
--   prop:block (ii): $n_+(Q) \le p$
-- statement:
--   In the abstract zero-side data `ZeroBlockData` of the window $\mathcal{Z}(I')$ (multiplicities $m_z$, evaluation vectors $u_z$, involution $\sigma = (\rho \mapsto 1 - \bar\rho)$), let $A = \sum_z m_z u_z u_z^{\mathsf T}$ be the window matrix and let
--   $$Q \;=\; c^{-1} \Bigl( A - \sum_{z \text{ on-line}} m_z\, u_z u_z^{\mathsf T} \Bigr) \qquad (\text{`blockQ c`}),$$
--   the normalised sum of the off-line pair contributions; at instantiation $c = aL^2$, so that $\hat A = A/(aL^2) = P + Q$ in the units of [eq:hatunits]. $Q$ is Hermitian (real symmetric), and $n_+ = $ `posIndex` counts its strictly positive eigenvalues. $p$ is the number of off-line pairs $\{\rho, 1 - \bar\rho\}$ (given by a `PairReps` choice $P$ of representatives).
--
--   **Statement.** For every $c > 0$,
--   $$n_+(Q) \;\le\; p.$$
--   As in the paper: the form $c \mapsto c^* Q c$ is the pull-back under the evaluation map of the direct sum of the $p$ hyperbolic $2\times 2$ blocks alone, so the bound follows from Lemma [lem:inertia] — in Lean, from $Q = c^{-1}(X - Y)$ with $X, Y \succeq 0$ and $\operatorname{rank} X \le p$, via `posIndex_sub_le_rank`.
--
--   **Role.** Part (ii) of prop:block; packaged by `blockInputsAt` in the module `Zeta23.ZeroSide` into `Assembly.BlockInputs` for the variational argument of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ZeroSide.lean#L544-L555, docstring tags [prop:block], [lem:inertia]

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

theorem Zeta23.ZeroSide.ZeroBlockData.posIndex_blockQ_le {c : ℝ} (hc : 0 < c) :
    posIndex (D.blockQ_isHermitian c) ≤ P.p := by sorry
