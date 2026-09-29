-- Prove2me | Theorems.Thm_Zeta23_MuInts_integral_main_sq_eq
-- name    : Zeta23.MuInts.integral_main_sq_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:56:45.166403+00:00
-- url     : https://prove2.me/theorems/b0fefc06-ea50-4794-a162-6d61a849542d
-- title:
--   FTC evaluation $\int_T^{2T} \log^2\frac{\tau}{2\pi}\,d\tau = T(\ell_1^2 + 1 - 2\log^2 2)$
-- statement:
--   For $T > 0$, with $\ell_1 = \ell_1(T) := \log\frac{T}{2\pi} + 2\log 2 - 1$ (the project's `ell1`), the following exact evaluation holds:
--   $$\int_T^{2T} \Bigl(\log\frac{\tau}{2\pi}\Bigr)^{2} d\tau \;=\; T\,\bigl(\ell_1^2 + 1 - 2\log^2 2\bigr).$$
--   This is a fundamental-theorem-of-calculus computation with the antiderivative $\tau \mapsto \tau(\log^2\frac{\tau}{2\pi} - 2\log\frac{\tau}{2\pi} + 2)$; expressed through $\ell_1$ the answer is the main term $T\ell_1^2$ plus the exact constant defect $T(1 - 2\log^2 2)$.
--
--   It is the "FTC anchor" isolating the main term of the second moment of $\mu$: its consumer is `Zeta23.MuInts.int_mu_sq_of_stirling` in the module `Zeta23.GammaFacts.IntMu`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/IntMu.lean#L168-L223

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

theorem Zeta23.MuInts.integral_main_sq_eq {T : ℝ} (hT : 0 < T) :
    ∫ τ in T..(2 * T), Real.log (τ / (2 * Real.pi)) ^ 2
      = T * (ell1 T ^ 2 + 1 - 2 * Real.log 2 ^ 2) := by sorry
