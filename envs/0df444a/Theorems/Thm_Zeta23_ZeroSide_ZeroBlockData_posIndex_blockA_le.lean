-- Prove2me | Theorems.Thm_Zeta23_ZeroSide_ZeroBlockData_posIndex_blockA_le
-- name    : Zeta23.ZeroSide.ZeroBlockData.posIndex_blockA_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:53:51.104561+00:00
-- url     : https://prove2.me/theorems/dfcac681-579e-479e-b4c8-805a1c3116d1
-- title:
--   prop:block (i): $n_+(A) \le s_1 + s_2 + p$
-- statement:
--   Setup (`ZeroBlockData ι d`, the abstract zero-side data of the window $\mathcal{Z}(I')$): a finite index type $\iota$ of distinct zeros with multiplicities $m_z \ge 1$, evaluation vectors $u_z = v(z) \in \mathbb{C}^d$ (at instantiation $u_\rho = (\hat\varphi(\gamma_\rho - \tau_k))_k$), and the involution $\sigma$ ($\rho \mapsto 1 - \bar\rho$) satisfying $m \circ \sigma = m$ and $v(\sigma z) = \overline{v(z)}$. The matrix [eq:AE] is
--   $$A \;=\; \sum_z m_z\, u_z u_z^{\mathsf T}$$
--   (transpose, **not** conjugate-transpose; `blockA`), which is Hermitian, indeed real symmetric. $n_+ = $ `posIndex` is the number of strictly positive eigenvalues. $s_1$ and $s_2$ count the on-line points ($\sigma z = z$, i.e. $\beta = 1/2$) with $m_z = 1$ and $m_z \ge 2$ respectively, and $p = \#R$ where $P$ is a choice of one representative per off-line pair $\{\rho, 1-\bar\rho\}$ (`PairReps`).
--
--   **Statement.**
--   $$n_+(A) \;\le\; s_1 + s_2 + p.$$
--   Positive scalings do not change $n_+$ (`posIndex_smul_pos`), so the same bound holds for the paper's normalisations $\tilde A = A/L$ and $\hat A = A/(aL^2)$. The Lean proof runs the paper's inertia argument through subadditivity of the positive index (`posIndex_add_le`, the corollary of [lem:inertia]): writing $A = P_0 + (X - Y)$ with $P_0 = \sum_{\text{on}} m\, u u^{\mathsf T} \succeq 0$ of rank $\le s_1 + s_2$ and $X - Y$ the pair part with $X \succeq 0$ of rank $\le p$, $Y \succeq 0$ (each hyperbolic block $m(uu^{\mathsf T} + \bar u \bar u^{\mathsf T}) = 2m(xx^{\mathsf T} - yy^{\mathsf T})$).
--
--   **Role.** This is part (i) of the paper's prop:block; in the module `Zeta23.ZeroSide` it is packaged by `blockInputsAt` into `Assembly.BlockInputs`, the zero-side input of the variational proof of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ZeroSide.lean#L428-L444, docstring tag [prop:block]

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

theorem Zeta23.ZeroSide.ZeroBlockData.posIndex_blockA_le : posIndex D.blockA_isHermitian ≤ D.s₁ + D.s₂ + P.p := by sorry
