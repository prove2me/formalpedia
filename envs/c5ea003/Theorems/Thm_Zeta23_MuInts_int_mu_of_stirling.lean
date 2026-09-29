-- Prove2me | Theorems.Thm_Zeta23_MuInts_int_mu_of_stirling
-- name    : Zeta23.MuInts.int_mu_of_stirling
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:56:39.054543+00:00
-- url     : https://prove2.me/theorems/96cae68e-15f8-45a8-8f9a-012c42dc5cd6
-- title:
--   First moment $\int_T^{2T} \mu = T\ell_1/(2\pi) + O(1/T)$, given Stirling
-- statement:
--   Let $\mu$ be the archimedean density [eq:mudef], and for $T > 0$ set $\ell_1 = \ell_1(T) := \log\frac{T}{2\pi} + 2\log 2 - 1$ (the project's `ell1`, chosen so that $N(T,2T) = T\ell_1/2\pi + O(l)$). The hypothesis `StirlingHyp` is the Stirling-type asymptotic for $\mu$: there is a constant $C_0$ with $\bigl|\mu(\tau) - \frac{1}{2\pi}\log\frac{|\tau|}{2\pi}\bigr| \le C_0/\tau^2$ for all $|\tau| \ge 1$.
--
--   The theorem asserts: assuming `StirlingHyp`, there exist constants $C$ and $T_0$ such that for all $T \ge T_0$,
--   $$\Bigl| \int_T^{2T} \mu(\tau)\, d\tau \;-\; \frac{T\,\ell_1}{2\pi} \Bigr| \;\le\; \frac{C}{T},$$
--   the integral being an interval (Bochner) integral. This is the first half of the paper's [eq:muints]: "$\int_T^{2T} \mu(\tau)\,d\tau = T\ell_1/(2\pi) + O(1/T)$".
--
--   The main term is evaluated exactly by the FTC anchor `Zeta23.MuInts.integral_main_eq`; the error integrates the $O(\tau^{-2})$ Stirling tail. The node feeds the assembly theorems `Zeta23.thmA0_cumulative` and `Zeta23.thmA1`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/IntMu.lean#L84-L166, docstring tag [eq:muints]

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

theorem Zeta23.MuInts.int_mu_of_stirling (hst : StirlingHyp) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(∫ τ in T..(2 * T), Zeta23.mu τ) - T * ell1 T / (2 * Real.pi)| ≤ C / T := by sorry
