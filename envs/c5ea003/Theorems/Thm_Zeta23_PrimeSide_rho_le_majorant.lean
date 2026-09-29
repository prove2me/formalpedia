-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_rho_le_majorant
-- name    : Zeta23.PrimeSide.rho_le_majorant
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:13:52.533852+00:00
-- url     : https://prove2.me/theorems/c3656769-a984-4031-9fa8-1d1674746583
-- title:
--   Pointwise majorant for $\rho$: $\rho(\tau) \le W(\tau - T) + W(2T - \tau) + \psi(\tau_d - \tau)^2$
-- statement:
--   **Setup.** A *setting* $p$ consists of a height $T$, a bandwidth ratio $\lambda$, and a ramp width $w$; from these one forms $l = \log(T/2\pi)$, $L = \lambda l$, $X = e^{L}$, the grid spacing $h = 2\pi/L$, the number of grid points $d = \lfloor LT/2\pi \rfloor$, the grid $\tau_k = T + kh$, and the window $I = [T, 2T]$. A *taper datum* $F$ packages the test-function data: $\hat{\varphi}$, $\Phi = \widehat{\varphi^2}$ (both real and even on $\mathbb{R}$), $A_\varphi = \varphi \star \varphi$, $g = \varphi^2 \star \varphi^2$, and the constants $a = L^{-1}\int \varphi^2$, $b = L^{-1}\int \varphi^4$ [eq:abdef].
--
--   $\psi(r) := \min\bigl(L,\ 2/|r|,\ c_\varrho/(w r^2)\bigr)$ is the taper majorant [eq:psidef], with the explicit value $\psi(0) = L$ guarding Lean's convention $2/0 = 0$; $c_\varrho \ge 4$ is the profile constant of [eq:phinorms]. The deficiency function is $\rho(\tau) := a L^2 - \sum_{k < d} \hat{\varphi}(\tau - \tau_k)^2$ (how far the grid sum of $\hat{\varphi}^2$ falls short of its Poisson-summation value $aL^2$), and $W(\Delta) := \psi(\Delta)^2 + h^{-1} \int_{(\Delta,\infty)} \psi(r)^2\, dr$; $\tau_d = T + d h$ is the first grid point beyond the window.
--
--   **Statement.** Assume the weak core local hypotheses `LocalHypsCoreW` (no upper cap on $\lambda$) and $T > 0$. Then for every $\tau \in [T, 2T]$,
--   $$\rho(\tau) \le W(\tau - T) + W(2T - \tau) + \psi(\tau_d - \tau)^2.$$
--   Thus $\rho$ is controlled by boundary-distance terms alone: away from the endpoints of $I = [T,2T]$ the grid sum nearly attains $a L^2$.
--
--   **Role.** The pointwise input to `Zeta23.PrimeSide.setIntegral_rho_div_gwt_le`, the weighted integral bound on $\rho$ used in the $\mathcal{E}_1$ estimate of [lem:ends] (§5.3), which controls the diagonal error in the second-moment computation of $\operatorname{tr}\tilde{G}^2$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsE1.lean#L296-L428

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

theorem Zeta23.PrimeSide.rho_le_majorant (hF : LocalHypsCoreW cϱ p F) (hT : 0 < p.T) {τ : ℝ}
    (hτ : τ ∈ Icc p.T (2 * p.T)) :
    rho p F τ ≤ Wfun cϱ p (τ - p.T) + Wfun cϱ p (2 * p.T - τ) + psiA cϱ p (p.tau p.d - τ) ^ 2 := by sorry
