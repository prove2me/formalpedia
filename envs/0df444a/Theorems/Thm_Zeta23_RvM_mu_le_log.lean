-- Prove2me | Theorems.Thm_Zeta23_RvM_mu_le_log
-- name    : Zeta23.RvM.mu_le_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:41:17.405054+00:00
-- url     : https://prove2.me/theorems/f63c18b1-abb1-40c7-906c-f6d4d762563e
-- title:
--   Logarithmic bound for the archimedean density: $|\mu(\tau)| \le C \log(\tau + 3)$ for $\tau \ge 1$
-- statement:
--   **Setup.** $\mu$ is the archimedean density of [eq:mudef]: $\mu(\tau) = \frac{1}{2\pi}\,\mathrm{Re}\,\psi\bigl(\tfrac14 + \tfrac{i\tau}{2}\bigr) - \frac{\log\pi}{2\pi}$, with $\psi = \Gamma'/\Gamma$ the digamma function. `GammaFacts` is the project's bundled hypothesis H-$\Gamma$ (proved elsewhere in the repository): Stirling-type facts about $\mu$, including $\bigl|\mu(\tau) - \frac{1}{2\pi}\log\frac{|\tau|}{2\pi}\bigr| \le C_0/\tau^2$ for $|\tau| \ge 1$.
--
--   **Statement.** Assuming `GammaFacts`, there exists a constant $C > 0$ such that for every real $\tau \ge 1$,
--
--   $$|\mu(\tau)| \;\le\; C \,\log(\tau + 3).$$
--
--   **Role.** A crude but uniform consequence of the Stirling field of H-$\Gamma$, used in `Zeta23.RvM.rvM_main_aux` to absorb the change between nearby contour heights: replacing an arbitrary height by a good height within distance one changes $\int \mu$ by at most $O(\log T)$, which is within the error term of the Riemann–von Mangoldt formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/RvM/GammaSide.lean#L164-L200

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_RvM_Defs
import Definitions.Def_Zeta23_RvM_GammaSide
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect

open Complex MeasureTheory Set
open scoped Interval
open Zeta23
open Zeta23.RvM

theorem Zeta23.RvM.mu_le_log (hΓ : Zeta23.GammaFacts) : ∃ C : ℝ, 0 < C ∧ ∀ τ : ℝ, 1 ≤ τ →
    |mu τ| ≤ C * Real.log (τ + 3) := by sorry
