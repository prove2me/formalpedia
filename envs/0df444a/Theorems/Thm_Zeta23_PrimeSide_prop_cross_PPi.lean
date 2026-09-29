-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_prop_cross_PPi
-- name    : Zeta23.PrimeSide.prop_cross_PPi
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:24:38.172117+00:00
-- url     : https://prove2.me/theorems/d925af99-28e0-4557-9096-d9bbacf5e86b
-- title:
--   [prop:cross] (iii): $\mathcal{M}[P_X,\Pi_X] \ll L\,X$
-- statement:
--   Work in the abstract prime-side setting: $p=(T,\lambda,w)$ with $L=\lambda\log(T/2\pi)$, $X=e^L$, window $I=[T,2T]$, taper data $F$, and seam form $\mathcal{M}[u_1,u_2]=\iint_{I\times I}\Phi(\tau-\tau')^2u_1(\tau)u_2(\tau')\,d\tau\,d\tau'$. Here $P_X(\tau)=-\tfrac1\pi\sum_{n\le X}\Lambda(n)n^{-1/2}\cos(\tau\log n)$ is the prime-power density [eq:Pdef] and $\Pi_X$ is the continuous correction density of [eq:Pidef].
--
--   Assume the Chebyshev–Mertens estimates H-cheb (the Stirling facts H-$\Gamma$ are carried for interface uniformity but unused) and $0<\lambda\le 1$. Then there is a constant $C$ such that uniformly for large $T$ — i.e. there is $T_0$ with the following for every setting $p$ at bandwidth ratio $\lambda$, $T\ge T_0$, and taper $F$ satisfying `LocalHypsCore` —
--   $$\bigl|\mathcal{M}[P_X,\Pi_X]\bigr|\ \le\ C\cdot L\,X.$$
--   The proof is the paper's sup-bound (§5.4): $|P_X|\le\sqrt{X}$ on $I$ (from H-cheb) and $|\Pi_X|\le 3\sqrt{X}/T$ on $I$ [eq:PiPfacts], giving $\le\sqrt{X}\cdot(3\sqrt{X}/T)\cdot T\cdot 2\pi bL\le 6\pi LX$.
--
--   This is part (iii) of the four cross-term bounds [prop:cross] in the six-term expansion of $\mathcal{M}=\mathcal{M}[\nu_X,\nu_X]$; its consumer is `concreteFacts`, the bundle assembled into the trace theorem [thm:traces].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA.lean#L426-L445, docstring tag [prop:cross]

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
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable (cϱ lam : ℝ)

theorem Zeta23.PrimeSide.prop_cross_PPi (_hΓ : Zeta23.GammaFacts) (hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T (Zeta23.PX p.X) (Zeta23.PiX p.X)| ≤ C * (p.L * p.X)) := by sorry
