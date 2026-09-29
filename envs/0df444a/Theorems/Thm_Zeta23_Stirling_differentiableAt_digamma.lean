-- Prove2me | Theorems.Thm_Zeta23_Stirling_differentiableAt_digamma
-- name    : Zeta23.Stirling.differentiableAt_digamma
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:54:19.674303+00:00
-- url     : https://prove2.me/theorems/271764c6-6f66-4363-812b-2d3010af6207
-- title:
--   Differentiability of the digamma function off the integers
-- statement:
--   Let $\psi = \Gamma'/\Gamma$ denote the complex digamma function (Mathlib's `Complex.digamma`). For every $z$ in the *integer complement* `Complex.integerComplement` — the set of complex numbers that are not integers — $\psi$ is complex-differentiable at $z$:
--   $$z \notin \mathbb{Z} \;\Longrightarrow\; \psi \text{ is differentiable at } z.$$
--
--   The reason is that $\Gamma$ is analytic and nonvanishing away from its poles, so its logarithmic derivative is analytic there; excluding all integers (rather than only the nonpositive ones, where the poles actually lie) gives a convenient uniform domain.
--
--   In the project this regularity fact supports the bound on $\mu'$ via the trigamma series (`Zeta23.MuFields.mu_deriv_bound`) and the continuity of the logarithmic derivative of the archimedean factor $\Gamma_{\mathbb R}$ along vertical lines in the explicit-formula argument (`Zeta23.WeilEF.continuous_logDeriv_GammaR_line`).
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Analytic/Stirling.lean#L28-L49

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

open Complex Filter Topology

theorem Zeta23.Stirling.differentiableAt_digamma {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    DifferentiableAt ℂ Complex.digamma z := by sorry
