-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_sub_mul_Aminus_eq
-- name    : Zeta23.PrimeSide.sub_mul_Aminus_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:04:39.210775+00:00
-- url     : https://prove2.me/theorems/c4bf8afd-d73c-4829-a719-87230a723a48
-- title:
--   Exact per-pair identity for $\theta \cdot A^-(y, y')$ in the $\mathcal{O}_1$ bound
-- statement:
--   **Setup.** For a continuous even profile $\Phi$ and $T \ge 0$, the difference-frequency half of $\mathcal{M}[\cos(\cdot\, y), \cos(\cdot\, y')]$ is
--   $$A^-(y, y') := \int_{[-T,\, T]} \Phi(x)^2\, J\bigl(y - y',\ x y;\ I \cap (I - x)\bigr)\, dx, \qquad J(\theta, c; \alpha, \beta) := \int_\alpha^\beta \cos(\theta t + c)\, dt,$$
--   where $I \cap (I - x) = [\max(T - x, T),\, \min(2T - x, 2T)]$. The four cosine/sine moments of $\Phi^2$ are
--   $$C^+(y) = \int_0^T \Phi(x)^2 \cos(x y)\, dx, \quad S^+(y) = \int_0^T \Phi(x)^2 \sin(x y)\, dx, \quad C^-(y) = \int_{-T}^0 \Phi(x)^2 \cos(x y)\, dx, \quad S^-(y) = \int_{-T}^0 \Phi(x)^2 \sin(x y)\, dx.$$
--
--   **Statement.** Write $\theta := y - y'$ and assume $\theta \ne 0$. Then, exactly,
--   $$\theta \cdot A^-(y, y') = \bigl[\sin(2\theta T)\, C^-(y) + \cos(2\theta T)\, S^-(y)\bigr] - \bigl[\sin(\theta T)\, C^-(y') + \cos(\theta T)\, S^-(y')\bigr] + \bigl[\sin(2\theta T)\, C^+(y') + \cos(2\theta T)\, S^+(y')\bigr] - \bigl[\sin(\theta T)\, C^+(y) + \cos(\theta T)\, S^+(y)\bigr].$$
--   This realizes the paper's §5.4 manipulation ("$n^{ix}(n/m)^{-ix^+}$ equals $m^{ix}$ for $x > 0$ and $n^{ix}$ for $x < 0$..."): the interval $[-T, T]$ is split at $0$, the sheared window being $[T - x,\, 2T]$ for $x \le 0$ and $[T,\, 2T - x]$ for $x \ge 0$.
--
--   **Role.** The exact algebraic identity underlying the off-diagonal bound $\mathcal{O}_1$ in the evaluation of $\mathcal{M}[P_X, P_X]$ ([prop:PP], §5.4); consumed by `Zeta23.PrimeSide.O1_bound`, which sums the resulting oscillatory moments over pairs of prime-power frequencies.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PPKernel.lean#L438-L487

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideB_PPKernel

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction ComplexConjugate
open Zeta23
open PrimeSide
variable {Φ : ℝ → ℝ} {T : ℝ}

theorem Zeta23.PrimeSide.sub_mul_Aminus_eq (hT : 0 ≤ T) (hΦ : Continuous Φ) {y y' : ℝ} (hθ : y - y' ≠ 0) :
    (y - y') * Aminus Φ T y y'
      = (Real.sin ((y - y') * (2 * T)) * Cm Φ T y + Real.cos ((y - y') * (2 * T)) * Sm Φ T y
          - (Real.sin ((y - y') * T) * Cm Φ T y' + Real.cos ((y - y') * T) * Sm Φ T y'))
        + (Real.sin ((y - y') * (2 * T)) * Cp Φ T y' + Real.cos ((y - y') * (2 * T)) * Sp Φ T y'
          - (Real.sin ((y - y') * T) * Cp Φ T y + Real.cos ((y - y') * T) * Sp Φ T y)) := by sorry
