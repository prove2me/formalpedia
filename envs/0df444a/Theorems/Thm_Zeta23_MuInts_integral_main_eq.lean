-- Prove2me | Theorems.Thm_Zeta23_MuInts_integral_main_eq
-- name    : Zeta23.MuInts.integral_main_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:56:28.14346+00:00
-- url     : https://prove2.me/theorems/4199d468-4cae-4312-ad6d-675be4298e66
-- title:
--   FTC evaluation $\int_T^{2T} \frac{1}{2\pi}\log\frac{\tau}{2\pi}\,d\tau = \frac{T\ell_1}{2\pi}$
-- statement:
--   For $T > 0$, with $\ell_1 = \ell_1(T) := \log\frac{T}{2\pi} + 2\log 2 - 1$ (the project's `ell1`), the following exact evaluation holds:
--   $$\int_T^{2T} \frac{1}{2\pi}\,\log\frac{\tau}{2\pi}\; d\tau \;=\; \frac{T\,\ell_1}{2\pi}.$$
--   This is a fundamental-theorem-of-calculus computation with the antiderivative $\tau \mapsto \frac{1}{2\pi}\,\tau\,(\log\frac{\tau}{2\pi} - 1)$; the specific combination $2\log 2 - 1$ inside $\ell_1$ is exactly what makes the identity exact (no error term).
--
--   It is the "FTC anchor" isolating the main term of the first moment of $\mu$: its consumer is `Zeta23.MuInts.int_mu_of_stirling` in the module `Zeta23.GammaFacts.IntMu`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/IntMu.lean#L27-L82

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_GammaFacts_IntMu
import Definitions.Def_Zeta23_GammaFacts_Series

open Zeta23
open MuInts
open MeasureTheory intervalIntegral

theorem Zeta23.MuInts.integral_main_eq {T : ℝ} (hT : 0 < T) :
    ∫ τ in T..(2 * T), (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))
      = T * ell1 T / (2 * Real.pi) := by sorry
