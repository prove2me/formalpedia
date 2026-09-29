-- Prove2me | Theorems.Thm_Zeta23_MuInts_int_mu_sq_of_stirling
-- name    : Zeta23.MuInts.int_mu_sq_of_stirling
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:56:50.600925+00:00
-- url     : https://prove2.me/theorems/b09510ac-0836-4fbb-a3cd-abbf024a7ed0
-- title:
--   Second moment $\int_T^{2T} \mu^2 = \frac{T\ell_1^2}{4\pi^2}\bigl(1 + O(l^{-2})\bigr)$, given Stirling
-- statement:
--   Let $\mu$ be the archimedean density [eq:mudef], and for $T > 0$ set $l = l(T) := \log\frac{T}{2\pi}$ and $\ell_1 = \ell_1(T) := l + 2\log 2 - 1$. The hypothesis `StirlingHyp` is the Stirling-type asymptotic $\bigl|\mu(\tau) - \frac{1}{2\pi}\log\frac{|\tau|}{2\pi}\bigr| \le C_0/\tau^2$ for $|\tau| \ge 1$.
--
--   The theorem asserts: assuming `StirlingHyp`, there exist constants $C$ and $T_0$ such that for all $T \ge T_0$,
--   $$\Bigl| \int_T^{2T} \mu(\tau)^2\, d\tau \;-\; \frac{T\,\ell_1^2}{4\pi^2} \Bigr| \;\le\; C \cdot \frac{T\,\ell_1^2 / (4\pi^2)}{l^2},$$
--   i.e. the second moment of $\mu$ over $[T,2T]$ equals its main term $T\ell_1^2/(4\pi^2)$ up to a relative error $O(l^{-2})$. This is the second half of the paper's [eq:muints]: "$\int_T^{2T} \mu(\tau)^2\,d\tau = (T\ell_1^2/4\pi^2)(1 + O(l^{-2}))$".
--
--   The exact main term rests on the FTC anchor `Zeta23.MuInts.integral_main_sq_eq` for $\int_T^{2T} \log^2(\tau/2\pi)\,d\tau$. Both moments of $\mu$ enter the mollified second-moment computation; this node feeds the assembly theorems `Zeta23.thmA0_cumulative` and `Zeta23.thmA1`.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/GammaFacts/IntMu.lean#L225-L521, docstring tag [eq:muints]

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
set_option maxHeartbeats 1600000

theorem Zeta23.MuInts.int_mu_sq_of_stirling (hst : StirlingHyp) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(∫ τ in T..(2 * T), Zeta23.mu τ ^ 2) - T * ell1 T ^ 2 / (4 * Real.pi ^ 2)|
        ≤ C * (T * ell1 T ^ 2 / (4 * Real.pi ^ 2)) / l T ^ 2 := by sorry
