-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_sum_psiA_shift_right
-- name    : Zeta23.PrimeSide.sum_psiA_shift_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:15:10.687027+00:00
-- url     : https://prove2.me/theorems/197dc98e-e7e9-467a-b201-3cbf5092fdef
-- title:
--   Right grid domination: $\sum_{k<d} \psi(\tau - \tau_k) \le \sum_{j<d} \psi((\tau - 2T) + jh)$ for $\tau \ge 2T$
-- statement:
--   **Setup.** A *setting* $p$ consists of a height $T$, a bandwidth ratio $\lambda$, and a ramp width $w$; from these one forms $l = \log(T/2\pi)$, $L = \lambda l$, $X = e^{L}$, the grid spacing $h = 2\pi/L$, the number of grid points $d = \lfloor LT/2\pi \rfloor$, the grid $\tau_k = T + kh$, and the window $I = [T, 2T]$. A *taper datum* $F$ packages the test-function data: $\hat{\varphi}$, $\Phi = \widehat{\varphi^2}$ (both real and even on $\mathbb{R}$), $A_\varphi = \varphi \star \varphi$, $g = \varphi^2 \star \varphi^2$, and the constants $a = L^{-1}\int \varphi^2$, $b = L^{-1}\int \varphi^4$ [eq:abdef].
--
--   $\psi(r) := \min\bigl(L,\ 2/|r|,\ c_\varrho/(w r^2)\bigr)$ is the taper majorant [eq:psidef], with the explicit value $\psi(0) = L$ guarding Lean's convention $2/0 = 0$; $c_\varrho \ge 4$ is the profile constant of [eq:phinorms].
--
--   **Statement.** Assume $L \ge 0$, $c_\varrho \ge 0$, $w > 0$. Let $T, h, \tau$ be reals with $h > 0$ and $\tau \ge 2T$, and let $d$ be a natural number whose grid points satisfy $T + k h \le 2T$ for all $k < d$. Then
--   $$\sum_{k = 0}^{d-1} \psi\bigl(\tau - (T + k h)\bigr) \;\le\; \sum_{j = 0}^{d-1} \psi\bigl((\tau - 2T) + j h\bigr).$$
--   For $\tau$ to the right of the window, reflecting the summation index shows each distance $\tau - (T + kh)$ dominates the corresponding $(\tau - 2T) + jh$, and $\psi$ is antitone on $[0, \infty)$.
--
--   **Role.** Reduces sums of shifted majorants over the grid, for points beyond the right endpoint $2T$, to a standardized arithmetic progression anchored at the distance $\tau - 2T$; consumed by `Zeta23.PrimeSide.dom_right` in the off-window ($\mathcal{E}_2$-side) tail estimates of [lem:ends].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsWeighted.lean#L215-L239

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
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem Zeta23.PrimeSide.sum_psiA_shift_right (hL : 0 ≤ p.L) (hc : 0 ≤ cϱ) (hw : 0 < p.w)
    {T h τ : ℝ} (hh : 0 < h) (hτ : 2 * T ≤ τ) {d : ℕ}
    (hgrid : ∀ k : ℕ, k < d → T + k * h ≤ 2 * T) :
    ∑ k ∈ Finset.range d, psiA cϱ p (τ - (T + k * h))
      ≤ ∑ j ∈ Finset.range d, psiA cϱ p ((τ - 2 * T) + j * h) := by sorry
