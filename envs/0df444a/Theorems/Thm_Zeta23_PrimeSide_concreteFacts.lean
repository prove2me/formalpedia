-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_concreteFacts
-- name    : Zeta23.PrimeSide.concreteFacts
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:29:04.980967+00:00
-- url     : https://prove2.me/theorems/0089ad2d-bc29-4c9b-936a-532e6c9665c7
-- title:
--   The prime-side trace facts hold for the concrete data
-- statement:
--   Let $P = (\varrho, \lambda, w)$ be a fixed parameter triple with `P.Valid` (a $C^3$ taper profile $\varrho$, $0 < \lambda \le 1$, $w \ge 1$), and let $Z$ be an abstract zero configuration (`ZeroConfig`: a reflection-symmetric multiset of points in the critical strip with locally finite ordinates, standing in for the nontrivial zeros of $\zeta$). Assume the paper's published analytic inputs `PaperInputs Z` (of which only H-RvM, H-Γ, H-cheb and H-MV are used here), and assume `LocalHypsEventually`: the taper facts `LocalHyps` hold for the concrete data $(P.\mathrm{toSetting}\, T,\, P.\mathrm{localFun}\, T)$ for all sufficiently large $T$ (proved elsewhere in the repository, in `Zeta23/PrimeSideA/Bridge.lean`).
--
--   The conclusion is `Facts (concreteData P Z)`: the full bundle of hypotheses of the [thm:traces] assembly holds for the concrete prime-side data — the actual traces $\operatorname{tr}\tilde G$, $\operatorname{tr}\tilde G^2$, the seam form $\mathcal{M}$ and its six bilinear pieces, $\int_T^{2T}\mu^2$, $\sum_{n \le X}\Lambda(n)^2 n^{-1} g(\log n)$, and $N(T, 2T)$ of $Z$. Concretely this comprises, each in explicit-constant `EvBound` form: [eq:abdef], the Riemann–von Mangoldt count [eq:RvM], the second moment [eq:muints], the first trace [prop:trace], the ends lemma [lem:ends], the bilinear splitting [eq:Msplit], the diagonal evaluations [prop:mumu] and [prop:PP] with its sandwich bounds, and the four cross-term bounds [prop:cross]. The Section 5 sub-results it packages are proved elsewhere in the repository.
--
--   This is the gateway from the analytic Sections 5 work to the final assembly: it is consumed directly by `Zeta23.thmA3` and `Zeta23.thmA3_cumulative`, the headline forms of Theorem A (more than $2/3 - \epsilon$ of the zeros in $(T, 2T]$ on the critical line).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/Traces.lean#L93-L196

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideA_EndsCore
import Definitions.Def_Zeta23_PrimeSideA_EndsE1
import Definitions.Def_Zeta23_PrimeSideA_EndsE2
import Definitions.Def_Zeta23_PrimeSideA_EndsNu
import Definitions.Def_Zeta23_PrimeSideB
import Definitions.Def_Zeta23_PrimeSideB_Concrete
import Definitions.Def_Zeta23_PrimeSideB_PP
import Definitions.Def_Zeta23_PrimeSideB_PPKernel
import Definitions.Def_Zeta23_PrimeSideB_Traces
import Definitions.Def_Zeta23_PrimeSideTemp

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
open PaperParams
variable (P : Params)
variable {P}

theorem Zeta23.PrimeSide.concreteFacts {cϱ : ℝ} {Z : ZeroConfig} (hP : P.Valid) (inp : PaperInputs Z)
    (hLoc : LocalHypsEventually cϱ P) : Facts (concreteData P Z) := by sorry
