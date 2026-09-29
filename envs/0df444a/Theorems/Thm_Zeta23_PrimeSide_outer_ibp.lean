-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_outer_ibp
-- name    : Zeta23.PrimeSide.outer_ibp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:11:28.660592+00:00
-- url     : https://prove2.me/theorems/b8e64bf1-1a16-4671-9571-3cf055c5658f
-- title:
--   Integration by parts in $\tau$ against $(\Phi^2)'(\tau-\tau')$
-- statement:
--   Let $\Phi:\mathbb{R}\to\mathbb{R}$ be continuously differentiable ($C^1$), let $u:\mathbb{R}\to\mathbb{R}$ be $C^1$, fix a height $T$ and a parameter $\tau'\in\mathbb{R}$.
--
--   Then the interval integral of $u$ against the derivative of the squared taper transform satisfies the exact integration-by-parts identity
--   $$\int_T^{2T}u(\tau)\,(\Phi^2)'(\tau-\tau')\,d\tau\ =\ u(2T)\,\Phi(2T-\tau')^2\ -\ u(T)\,\Phi(T-\tau')^2\ -\ \int_T^{2T}u'(\tau)\,\Phi(\tau-\tau')^2\,d\tau,$$
--   where $(\Phi^2)'$ denotes the derivative of $x\mapsto\Phi(x)^2$.
--
--   This is the outer of the two integrations by parts in the paper's treatment of the cross term $\mathcal{M}[\mu,P_X]$ ("integrating by parts in $\tau$", §5.4). In module `Zeta23.PrimeSideA.CrossMuPCore` it is consumed by `abs_Mform_cos_phase_le`, the oscillatory bound for $\mathcal{M}[u,\cos(\cdot\,y)]$ that drives [prop:cross] (i), the estimate $\mathcal{M}[\mu,P_X]\ll l\sqrt{X}$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/CrossMuPCore.lean#L66-L88

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

open MeasureTheory Real Set Finset
open scoped BigOperators
variable {Φ : ℝ → ℝ} {T : ℝ}

theorem Zeta23.PrimeSide.outer_ibp (hΦ : ContDiff ℝ 1 Φ) {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (τ' : ℝ) :
    ∫ τ in T..(2 * T), u τ * deriv (fun x => Φ x ^ 2) (τ - τ')
      = u (2 * T) * Φ (2 * T - τ') ^ 2 - u T * Φ (T - τ') ^ 2
        - ∫ τ in T..(2 * T), deriv u τ * Φ (τ - τ') ^ 2 := by sorry
