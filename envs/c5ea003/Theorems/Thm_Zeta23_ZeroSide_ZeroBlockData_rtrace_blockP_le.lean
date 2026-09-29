-- Prove2me | Theorems.Thm_Zeta23_ZeroSide_ZeroBlockData_rtrace_blockP_le
-- name    : Zeta23.ZeroSide.ZeroBlockData.rtrace_blockP_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:54:31.650673+00:00
-- url     : https://prove2.me/theorems/23530840-2df2-4c5e-931d-aa2f944a2518
-- title:
--   prop:block (ii): $\operatorname{tr} P \le N_{\mathrm{on}}(I')$
-- statement:
--   In the abstract zero-side data `ZeroBlockData`, let
--   $$P \;=\; c^{-1} \sum_{z \text{ on-line}} m_z\, u_z u_z^{\mathsf T} \qquad (\text{`blockP c`}),$$
--   the normalised on-line part of the window matrix (at instantiation $c = aL^2$, so $P$ is the matrix of the same name in the paper's proof of prop:block (ii)). Here `rtrace` is the real part of the trace (the full trace, since $P$ is Hermitian), and $N_{\mathrm{on}}(I') = \sum_{z \text{ on-line}} m_z$ (`Non`) is the multiplicity count of the on-line zeros.
--
--   **Statement.** If $c > 0$ and the Poisson bound holds — for every on-line $z$,
--   $$\sum_{k} \| v(z)_k \|^2 \;\le\; c$$
--   — then $\operatorname{tr} P \le N_{\mathrm{on}}(I')$.
--
--   The Poisson input enters *only* through the hypothesis: at instantiation, $\sum_{0 \le k < d} \hat\varphi(\gamma_\rho - \tau_k)^2$ is a finite partial sum of the nonnegative series whose full sum over $k \in \mathbb{Z}$ equals exactly $aL^2$ by [lem:poisson], so the trace computation $\operatorname{tr} P = c^{-1} \sum m_z \sum_k \|v(z)_k\|^2 \le \sum m_z$ goes through.
--
--   **Role.** Together with $\operatorname{rank} P \le s_1 + s_2$ and $n_+(Q) \le p$ this is part (ii) of prop:block; it is packaged by `blockInputsAt` in the module `Zeta23.ZeroSide` into `Assembly.BlockInputs`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ZeroSide.lean#L509-L525, docstring tag [lem:poisson]

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

theorem Zeta23.ZeroSide.ZeroBlockData.rtrace_blockP_le {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    rtrace (D.blockP c) ≤ (D.Non : ℝ) := by sorry
