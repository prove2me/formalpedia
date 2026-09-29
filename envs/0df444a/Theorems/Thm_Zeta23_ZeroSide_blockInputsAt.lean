-- Prove2me | Theorems.Thm_Zeta23_ZeroSide_blockInputsAt
-- name    : Zeta23.ZeroSide.blockInputsAt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:54:55.958693+00:00
-- url     : https://prove2.me/theorems/dad4ffb6-23cc-4af9-88a2-9bad5cd5cad0
-- title:
--   prop:block and [eq:Ncount] packaged as block inputs at height $T$
-- statement:
--   Let $Z$ be a zero configuration, $P$ a parameter choice (taper profile, exponent $\lambda$, ramp width $w$), and $T$ a real height. The window is $\mathcal{Z}(I')$ with $I' = (T - D_0, 2T + D_0]$, $D_0 = \sqrt{T}$, and the window matrix is $A = \sum_{\rho \in \mathcal{Z}(I')} m_\rho u_\rho u_\rho^{\mathsf T}$ with $u_\rho = (\hat\varphi(\gamma_\rho - \tau_k))_{0 \le k < d}$ [eq:AE]. The analytic hypotheses are:
--   - `PhiHatConj`: $\hat\varphi(\bar z) = \overline{\hat\varphi(z)}$ for all $z$;
--   - `PhiHatReal`: $\hat\varphi$ is real on the real axis;
--   - `PoissonSq` ([lem:poisson]): for every real $\gamma$, $\sum_{k \in \mathbb{Z}} \hat\varphi(\gamma - \tau_k)^2 = a L^2$ (as a `HasSum`);
--   - $0 < L(T)$ and $0 < a(T) L(T)^2$.
--
--   **Statement.** Under these hypotheses, `Assembly.BlockInputs Z P T` holds: the record consumed by the abstract Theorem A assembly, consisting of (in hat units $\hat A = A/(aL^2)$) a decomposition $\hat A = P + Q$ with $P \succeq 0$, $\operatorname{rank} P \le s_1 + s_2$, $\operatorname{tr} P \le N_{\mathrm{on}}(I')$, $Q$ Hermitian with $n_+(Q) \le p$, and $N_{\mathrm{on}}(I') + 2p \le N(I')$; and (in tilde units $\tilde A = A/L$) $n_+(\tilde A) \le s_1 + s_2 + p$, $\operatorname{rank} \tilde A \le \#\mathcal{Z}(I')$, and $s_1 + 2 s_2 + 2p \le N(I')$ [eq:Ncount]. Here $s_1, s_2$ count the on-line simple and multiple zeros of the window and $p$ the off-line pairs.
--
--   **Role.** This is the packaging theorem of the module `Zeta23.ZeroSide`: prop:block (i)+(ii) and [eq:Ncount], stated exactly as `Assembly.thmA_abstract` consumes them. It feeds `eventually_blockInputs_of` (the eventually-in-$T$ export used by Main); the analytic hypotheses are discharged from Taper/Poisson in `Zeta23/ZeroSide/Final.lean`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ZeroSide.lean#L957-L970, docstring tags [prop:block], [eq:Ncount]

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
open Zeta23

theorem Zeta23.ZeroSide.blockInputsAt (Z : ZeroConfig) (P : Params) (T : ℝ)
    (hconj : PhiHatConj T P) (hreal : PhiHatReal T P) (hPois : PoissonSq T P)
    (hL : 0 < P.L T) (hc : 0 < P.a T * P.L T ^ 2) :
    Assembly.BlockInputs Z P T := by sorry
