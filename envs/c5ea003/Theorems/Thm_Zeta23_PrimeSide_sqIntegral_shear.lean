-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_sqIntegral_shear
-- name    : Zeta23.PrimeSide.sqIntegral_shear
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:03:02.967815+00:00
-- url     : https://prove2.me/theorems/eb261516-5155-4148-a1a3-bbfd375ffce9
-- title:
--   Shear and Fubini: $\iint_{I\times I} \Phi(\tau-\tau')^2 G(\tau,\tau') = \int_{\mathbb{R}} \Phi(x)^2 \int_{I \cap (I-x)} G(x+\tau', \tau')\, d\tau'\, dx$
-- statement:
--   **Setup.** $I = [T, 2T]$; for an offset $x$, the sheared window is $I \cap (I - x) = [\max(T - x,\, T),\ \min(2T - x,\ 2T)]$ (Lean's `Ix T x`; equal to $[T + x^-,\, 2T - x^+]$ for $|x| < T$ and empty for $|x| > T$). $\Phi, G$ are real-valued with $G$ defined on $\mathbb{R}^2$.
--
--   **Statement.** For $\Phi$ and $G$ continuous,
--   $$\iint_{I \times I} \Phi(\tau - \tau')^2\, G(\tau, \tau')\, d\tau\, d\tau' \;=\; \int_{\mathbb{R}} \Phi(x)^2 \left( \int_{I \cap (I - x)} G(x + \tau',\, \tau')\, d\tau' \right) dx.$$
--   This is the substitution $\tau = \tau' + x$ of §5.4 ("noting that for fixed $x$ the variable $\tau'$ ranges over $I \cap (I - x)$"), justified by Fubini and the fact that the shear $(x, \tau') \mapsto (x + \tau', \tau')$ preserves Lebesgue measure on $\mathbb{R}^2$.
--
--   **Role.** The change of variables that turns the bilinear form $\mathcal{M}[\cdot,\cdot]$ into a single $x$-integral against $\Phi(x)^2$; consumed by `Zeta23.PrimeSide.Mform_cos_cos` (the per-frequency-pair evaluation of $\mathcal{M}[P_X, P_X]$ in [prop:PP]) and by `Zeta23.PrimeSide.mumu_core` ([prop:mumu]).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideB/PPKernel.lean#L111-L150

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

theorem Zeta23.PrimeSide.sqIntegral_shear (hΦ : Continuous Φ) {G : ℝ × ℝ → ℝ} (hG : Continuous G) :
    ∫ q in Icc T (2 * T) ×ˢ Icc T (2 * T), Φ (q.1 - q.2) ^ 2 * G q
      = ∫ x, Φ x ^ 2 * ∫ τ' in Ix T x, G (x + τ', τ') := by sorry
