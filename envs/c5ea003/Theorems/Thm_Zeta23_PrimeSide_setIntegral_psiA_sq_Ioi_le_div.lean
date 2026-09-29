-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_setIntegral_psiA_sq_Ioi_le_div
-- name    : Zeta23.PrimeSide.setIntegral_psiA_sq_Ioi_le_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:09:21.517995+00:00
-- url     : https://prove2.me/theorems/bc74703e-52a4-46e2-9d78-f6d7a2dc3796
-- title:
--   Tail of the squared majorant: $\int_\Delta^\infty \psi^2 \le (c_\varrho/w)^2/(3\Delta^3)$
-- statement:
--   **Setup.** A *setting* $p$ consists of a height $T$, a bandwidth ratio $\lambda$, and a ramp width $w$; from these one forms $l = \log(T/2\pi)$, $L = \lambda l$, $X = e^{L}$, the grid spacing $h = 2\pi/L$, the number of grid points $d = \lfloor LT/2\pi \rfloor$, the grid $\tau_k = T + kh$, and the window $I = [T, 2T]$. A *taper datum* $F$ packages the test-function data: $\hat{\varphi}$, $\Phi = \widehat{\varphi^2}$ (both real and even on $\mathbb{R}$), $A_\varphi = \varphi \star \varphi$, $g = \varphi^2 \star \varphi^2$, and the constants $a = L^{-1}\int \varphi^2$, $b = L^{-1}\int \varphi^4$ [eq:abdef].
--
--   $\psi(r) := \min\bigl(L,\ 2/|r|,\ c_\varrho/(w r^2)\bigr)$ is the taper majorant [eq:psidef], with the explicit value $\psi(0) = L$ guarding Lean's convention $2/0 = 0$; $c_\varrho \ge 4$ is the profile constant of [eq:phinorms].
--
--   **Statement.** Assume the weak core local hypotheses `LocalHypsCoreW` and let $\Delta > 0$. Then
--   $$\int_{(\Delta,\, \infty)} \psi(r)^2\, dr \le \frac{(c_\varrho/w)^2}{3\, \Delta^3}.$$
--   This integrates the tail of the branch $\psi(r)^2 \le (c_\varrho/(w r^2))^2$.
--
--   **Role.** A leaf tail estimate consumed by `Zeta23.PrimeSide.W1d` in the $\mathcal{E}_1$ boundary-weight analysis of [lem:ends] (module `EndsCore`), where the tail integral of $\psi^2$ appears inside the boundary majorant $W(\Delta) = \psi(\Delta)^2 + h^{-1}\int_{(\Delta,\infty)}\psi^2$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsCore.lean#L491-L510

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

theorem Zeta23.PrimeSide.setIntegral_psiA_sq_Ioi_le_div (hF : LocalHypsCoreW cϱ p F) {Δ : ℝ} (hΔ : 0 < Δ) :
    ∫ r in Set.Ioi Δ, psiA cϱ p r ^ 2 ≤ (cϱ / p.w) ^ 2 / (3 * Δ ^ 3) := by sorry
