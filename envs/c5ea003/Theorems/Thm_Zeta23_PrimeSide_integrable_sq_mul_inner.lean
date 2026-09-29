-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_integrable_sq_mul_inner
-- name    : Zeta23.PrimeSide.integrable_sq_mul_inner
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:22:31.274315+00:00
-- url     : https://prove2.me/theorems/a9430c62-b0b4-479c-9ce7-d0f6025f09df
-- title:
--   Integrability of the sheared integrand $\Phi(x)^2\int_{I\cap(I-x)}G$
-- statement:
--   Fix a real height $T$ and write $I=[T,2T]$. For an offset $x\in\mathbb{R}$ let $I_x := I\cap(I-x)=[\max(T-x,T),\ \min(2T-x,2T)]$ be the window over which $\tau'$ ranges after the shear substitution $\tau=\tau'+x$ in a double integral over $I\times I$ (§5.4).
--
--   Let $\Phi:\mathbb{R}\to\mathbb{R}$ and $G:\mathbb{R}\times\mathbb{R}\to\mathbb{R}$ be continuous. Then the sheared outer integrand
--   $$x\ \longmapsto\ \Phi(x)^2\int_{I_x}G(x+\tau',\tau')\,d\tau'$$
--   is Lebesgue integrable on $\mathbb{R}$.
--
--   Together with the shear–Fubini identity `sqIntegral_shear` (which rewrites $\iint_{I\times I}\Phi(\tau-\tau')^2\,G(\tau,\tau')$ as $\int_{\mathbb{R}}\Phi(x)^2\int_{I_x}G(x+\tau',\tau')\,d\tau'\,dx$), this guarantees that the outer integral produced by the substitution is a genuine Lebesgue integral. In the project (module `Zeta23.PrimeSideB.PPKernel`) it is consumed by `mumu_core`, the core estimate of [prop:mumu] evaluating the diagonal form $\mathcal{M}[\mu,\mu]$.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PPKernel.lean#L152-L182

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

theorem Zeta23.PrimeSide.integrable_sq_mul_inner (hΦ : Continuous Φ) {G : ℝ × ℝ → ℝ} (hG : Continuous G) :
    Integrable (fun x => Φ x ^ 2 * ∫ τ' in Ix T x, G (x + τ', τ')) := by sorry
