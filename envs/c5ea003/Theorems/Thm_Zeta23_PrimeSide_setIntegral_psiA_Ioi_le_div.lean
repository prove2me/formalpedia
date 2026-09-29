-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_setIntegral_psiA_Ioi_le_div
-- name    : Zeta23.PrimeSide.setIntegral_psiA_Ioi_le_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:07:58.292602+00:00
-- url     : https://prove2.me/theorems/63dc4561-0bd7-4510-b43e-0b1583d9d7a0
-- title:
--   Tail of the taper majorant: $\int_\Delta^\infty \psi \le c_\varrho/(w\Delta)$
-- statement:
--   **Setup.** A *setting* $p$ consists of a height $T$, a bandwidth ratio $\lambda$, and a ramp width $w$; from these one forms $l = \log(T/2\pi)$, $L = \lambda l$, $X = e^{L}$, the grid spacing $h = 2\pi/L$, the number of grid points $d = \lfloor LT/2\pi \rfloor$, the grid $\tau_k = T + kh$, and the window $I = [T, 2T]$. A *taper datum* $F$ packages the test-function data: $\hat{\varphi}$, $\Phi = \widehat{\varphi^2}$ (both real and even on $\mathbb{R}$), $A_\varphi = \varphi \star \varphi$, $g = \varphi^2 \star \varphi^2$, and the constants $a = L^{-1}\int \varphi^2$, $b = L^{-1}\int \varphi^4$ [eq:abdef].
--
--   $\psi(r) := \min\bigl(L,\ 2/|r|,\ c_\varrho/(w r^2)\bigr)$ is the taper majorant [eq:psidef], with the explicit value $\psi(0) = L$ guarding Lean's convention $2/0 = 0$; $c_\varrho \ge 4$ is the profile constant of [eq:phinorms].
--
--   **Statement.** Assume the weak core local hypotheses `LocalHypsCoreW` and let $\Delta > 0$. Then
--   $$\int_{(\Delta,\, \infty)} \psi(r)\, dr \le \frac{c_\varrho}{w\, \Delta}.$$
--   This follows from the branch $\psi(r) \le c_\varrho/(w r^2)$ of the definition of $\psi$ by integrating the tail.
--
--   **Role.** A leaf tail estimate consumed by `Zeta23.PrimeSide.Sgrid_mul_le_Mnear` in the $\mathcal{E}_2$/near-diagonal analysis of [lem:ends] (module `EndsCore`), where sums of $\psi$ over grid points are compared with integrals of $\psi$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsCore.lean#L386-L403

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
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
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

open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open PrimeSide
variable {cϱ : ℝ} (p : Setting) (F : LocalFun) (ν : ℝ → ℝ)
variable {p F ν}
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem Zeta23.PrimeSide.setIntegral_psiA_Ioi_le_div (hF : LocalHypsCoreW cϱ p F) {Δ : ℝ} (hΔ : 0 < Δ) :
    ∫ r in Set.Ioi Δ, psiA cϱ p r ≤ cϱ / (p.w * Δ) := by sorry
