-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_lem_ends
-- name    : Zeta23.PrimeSide.lem_ends
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:21:12.234525+00:00
-- url     : https://prove2.me/theorems/a82714a4-10f8-4454-b042-763fcf3298df
-- title:
--   End effects [lem:ends]: $\operatorname{tr}\widetilde{G}^2 = \mathcal{M} + O(L\,l\log l\,(l^2+X))$
-- statement:
--   Work in the abstract prime-side setting of §5: $p=(T,\lambda,w)$ with $l=\log(T/2\pi)$, $L=\lambda l$, $X=e^L$, grid points $\tau_k=T+2\pi k/L$ for $0\le k<d=\lfloor LT/2\pi\rfloor$, window $I=[T,2T]$, and taper data $F=(\hat\varphi,\Phi,A_\varphi,g,a,b)$. The prime-side matrix has entries $G_{kl}=\int_{\mathbb{R}}\hat\varphi(\tau-\tau_k)\hat\varphi(\tau-\tau_l)\,\nu_X(\tau)\,d\tau$ with the concrete density $\nu_X=\mu+\Pi_X+P_X$ [eq:nudef], and $\operatorname{tr}\widetilde{G}^2 = L^{-2}\sum_{0\le k,l<d}G_{kl}^2$. The seam object is $\mathcal{M}:=\iint_{I\times I}\Phi(\tau-\tau')^2\,\nu_X(\tau)\,\nu_X(\tau')\,d\tau\,d\tau'$.
--
--   Assume the Stirling facts H-$\Gamma$ for $\mu$ (`Zeta23.GammaFacts`), the Chebyshev–Mertens estimates H-cheb (carried for interface uniformity), and $0<\lambda\le 1$. Then there is a constant $C$ such that uniformly for large $T$ — precisely, there is $T_0$ such that for every setting $p$ with bandwidth ratio $\lambda$, $T\ge T_0$, and every taper $F$ satisfying the core hypotheses `LocalHypsCore` —
--   $$\Bigl|\operatorname{tr}\widetilde{G}^2-\mathcal{M}\Bigr|\ \le\ C\,L\,l\,\log l\,\bigl(l^2+X\bigr).$$
--
--   This is the paper's [lem:ends] (§5.3) verbatim, obtained by instantiating the $\nu$-generic form `lem_ends_nu` with $\nu:=\nu_X$ and $B:=l+4\sqrt{X}$ [eq:Bdef]. It is one of the pillars of the prime side: it feeds the six-term expansion `eq_Msplit` of $\mathcal{M}$, the trace estimates [prop:trace], the cross-term bounds [prop:cross], and the assembled `concreteFacts` consumed by [thm:traces].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Ends.lean#L138-L171, docstring tag [lem:ends]

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
open scoped BigOperators
open Zeta23
open PrimeSide
variable (cϱ lam : ℝ)

theorem Zeta23.PrimeSide.lem_ends (hΓ : Zeta23.GammaFacts) (_hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |trGt2A p F - MtotalA p F| ≤ C * (p.L * p.l * Real.log p.l * (p.l ^ 2 + p.X))) := by sorry
