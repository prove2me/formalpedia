-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_localHyps_concrete
-- name    : Zeta23.PrimeSide.localHyps_concrete
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:36:54.492498+00:00
-- url     : https://prove2.me/theorems/00103904-3382-4468-b70a-15e2d848755d
-- title:
--   All of `LocalHyps` for the concrete taper data, field by field
-- statement:
--   Let $P$ be a valid parameter datum (taper profile $\varrho$, bandwidth ratio $0<\lambda\le 1$, ramp width $w\ge 1$), and let $T$ be any height satisfying the regime conditions $8w\le L(T)$ [eq:wrange], $l(T)\ge 1$ (i.e. $T\ge 2\pi e$), and $X(T)\ge 1$, where $l=\log(T/2\pi)$, $L=\lambda l$, $X=e^{L}$.
--
--   Then the concrete setting $(T,\lambda,w)$ and the concrete taper data $(\hat\varphi,\Phi,A_\varphi,g,a,b)$ built from $\varrho$ satisfy the complete hypothesis package `LocalHyps` at the profile constant $c_\varrho=4\|\varrho'\|_\infty+4\|\varrho''\|_1$: the majorant bounds $|\hat\varphi|,|\Phi|\le\psi=\min(L,2/|r|,c_\varrho/(wr^2))$ with their integral consequences [eq:psiints], the Plancherel/Fourier normalisations $\int\hat\varphi^2=2\pi aL$, $\int\Phi^2\cos(xy)\,dx=2\pi g(y)$, the plateau bounds $(L-2w-|y|)_+\le g\le A_\varphi\le(L-|y|)_+$ and $1-2w/L\le b\le a\le 1$, Poisson summation $\sum_{k\in\mathbb{Z}}\hat\varphi(\tau-\tau_k)\hat\varphi(\tau'-\tau_k)=L\,\Phi(\tau-\tau')$ [lem:poisson], and the $\Pi_X$ bound $|\Pi_X(\tau)|\le 3\sqrt{X}/(1+|\tau|)$ [eq:PiPfacts].
--
--   The proof is a field-by-field assembly from `Taper.lean`, `Poisson.lean` and `PiFacts.lean` (module `Zeta23.PrimeSideA.Bridge`); its immediate consumer is `localHypsEventually`, which upgrades it to "for all large $T$".
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/Bridge.lean#L46-L100

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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
import Definitions.Def_Zeta23_PrimeSideB_Concrete
import Definitions.Def_Zeta23_PrimeSideTemp

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide

theorem Zeta23.PrimeSide.localHyps_concrete {P : Params} (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T)
    (hl : 1 ≤ l T) (hX : 1 ≤ P.X T) : LocalHyps P.crho (P.toSetting T) (P.localFun T) := by sorry
