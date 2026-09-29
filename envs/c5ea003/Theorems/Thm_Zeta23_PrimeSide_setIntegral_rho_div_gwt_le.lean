-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_setIntegral_rho_div_gwt_le
-- name    : Zeta23.PrimeSide.setIntegral_rho_div_gwt_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:14:25.062295+00:00
-- url     : https://prove2.me/theorems/7ef706f3-4d4f-4df9-b246-c0b4d1c84fe2
-- title:
--   Weighted integral of the grid deficiency: $\int_I \rho(\tau)\,(1 + \min(\tau - T,\, 2T - \tau))^2\, d\tau$ bounded explicitly
-- statement:
--   **Setup.** A *setting* $p$ consists of a height $T$, a bandwidth ratio $\lambda$, and a ramp width $w$; from these one forms $l = \log(T/2\pi)$, $L = \lambda l$, $X = e^{L}$, the grid spacing $h = 2\pi/L$, the number of grid points $d = \lfloor LT/2\pi \rfloor$, the grid $\tau_k = T + kh$, and the window $I = [T, 2T]$. A *taper datum* $F$ packages the test-function data: $\hat{\varphi}$, $\Phi = \widehat{\varphi^2}$ (both real and even on $\mathbb{R}$), $A_\varphi = \varphi \star \varphi$, $g = \varphi^2 \star \varphi^2$, and the constants $a = L^{-1}\int \varphi^2$, $b = L^{-1}\int \varphi^4$ [eq:abdef].
--
--   $\psi(r) := \min\bigl(L,\ 2/|r|,\ c_\varrho/(w r^2)\bigr)$ is the taper majorant [eq:psidef], with the explicit value $\psi(0) = L$ guarding Lean's convention $2/0 = 0$; $c_\varrho \ge 4$ is the profile constant of [eq:phinorms]. The deficiency is $\rho(\tau) := a L^2 - \sum_{k<d} \hat{\varphi}(\tau - \tau_k)^2$, and the boundary weight is $g(\tau) := \bigl(1 + \min(\tau - T,\, 2T - \tau)\bigr)^{-2}$ (Lean's `gwt`), so $\rho/g = \rho(\tau)\,(1 + \min(\tau - T, 2T - \tau))^2$.
--
--   **Statement.** Assume the weak core local hypotheses `LocalHypsCoreW`, a `NuBound` datum for $\nu$ (present in the interface but unused in this proof), and $T \ge 1$. Then
--   $$\int_{[T,\,2T]} \frac{\rho(\tau)}{g(\tau)}\, d\tau \;\le\; 2\Bigl(4 L^2 + 4\bigl(\tfrac{c_\varrho}{w}\bigr)^2 + h^{-1}\Bigl(32 L + \tfrac43 \bigl(\tfrac{c_\varrho}{w}\bigr)^2 \log T\Bigr)\Bigr) + \Bigl(18 L^2 + 18 \bigl(\tfrac{c_\varrho}{w}\bigr)^2\Bigr).$$
--   The right-hand side collects the leaf integrals $W_{1a} + W_{1b} + h^{-1}(W_{1c} + W_{1d})$ (doubled for the two endpoints) plus the $W_3$ term from $\psi(\tau_d - \tau)^2$, via the pointwise majorant `rho_le_majorant`.
--
--   **Role.** The integrated form of the boundary-deficiency estimate; consumed by `Zeta23.PrimeSide.calE1_maj_bound`, which bounds the diagonal error $\mathcal{E}_1$ in the proof of [lem:ends] (§5.3), i.e. $\operatorname{tr}\tilde{G}^2 = \mathcal{M} + O(\cdots)$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsE1.lean#L433-L610

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

theorem Zeta23.PrimeSide.setIntegral_rho_div_gwt_le (hF : LocalHypsCoreW cϱ p F) (_hν : NuBound p B ν) (hT : 1 ≤ p.T) :
    ∫ τ in Icc p.T (2 * p.T), rho p F τ / gwt p τ
      ≤ 2 * (4 * p.L ^ 2 + 4 * (cϱ / p.w) ^ 2
            + (p.h)⁻¹ * (32 * p.L + 4 / 3 * (cϱ / p.w) ^ 2 * Real.log p.T))
        + (18 * p.L ^ 2 + 18 * (cϱ / p.w) ^ 2) := by sorry
