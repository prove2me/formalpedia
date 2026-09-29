-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_majK1_le
-- name    : Zeta23.PrimeSide.majK1_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:13:36.211601+00:00
-- url     : https://prove2.me/theorems/8fb5e333-082e-4cc6-b14c-824c79fe471f
-- title:
--   Pointwise bound for the $\mathcal{E}_1$ majorant kernel on $I\times I$
-- statement:
--   Work in the abstract prime-side setting: $p=(T,\lambda,w)$, taper data $F$ with the window-generic core hypotheses, window $I=[T,2T]$. Two auxiliary weights enter the $\mathcal{E}_1$ estimate of [lem:ends]: the Poisson-tail function $\rho(\tau):=aL^2-\sum_{0\le k<d}\hat\varphi(\tau-\tau_k)^2$ (the mass of the grid sum missing from $[0,d)$), and the boundary weight $g_{\mathrm{wt}}(\tau):=\bigl(1+\min(\tau-T,\,2T-\tau)\bigr)^{-2}$. The majorant kernel is
--   $$K_1(\tau,\tau'):=L^2\Bigl(\tfrac{\rho(\tau)}{g_{\mathrm{wt}}(\tau)}g_{\mathrm{wt}}(\tau')+g_{\mathrm{wt}}(\tau)\tfrac{\rho(\tau')}{g_{\mathrm{wt}}(\tau')}\Bigr)\,|\nu(\tau)|\,|\nu(\tau')|,$$
--   which dominates $|K^2-K_\infty^2|\,|\nu\nu'|$ by a weighted AM–GM argument.
--
--   Assume $\nu$ has level $B$ (i.e. $|\nu(\tau)|\le B+\log^+(|\tau|/4T)$, hence $|\nu|\le B$ on a neighbourhood of $I$) and $T>0$. Then for every point $(\tau,\tau')\in I\times I$:
--   $$K_1(\tau,\tau')\ \le\ L^2B^2\Bigl(\frac{\rho(\tau)}{g_{\mathrm{wt}}(\tau)}\,g_{\mathrm{wt}}(\tau')+g_{\mathrm{wt}}(\tau)\,\frac{\rho(\tau')}{g_{\mathrm{wt}}(\tau')}\Bigr).$$
--
--   In module `Zeta23.PrimeSideA.EndsE1` this strips the $\nu$-weights off the kernel; integrating the right-hand side over $I\times I$ gives `calE1_maj_bound` and hence the $\mathcal{E}_1\ll L^3B^2\,l$ part of [lem:ends].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsE1.lean#L231-L250

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
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideA_EndsCore
import Definitions.Def_Zeta23_PrimeSideA_EndsE1

open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem Zeta23.PrimeSide.majK1_le (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν) (hT : 0 < p.T)
    {q : ℝ × ℝ} (hq : q ∈ sqI p) :
    majK1 p F ν q ≤ p.L ^ 2 * B ^ 2 *
        (rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2)) := by sorry
