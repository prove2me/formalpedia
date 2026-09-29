-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_sum_grid_le_of_antitoneOn
-- name    : Zeta23.PrimeSide.sum_grid_le_of_antitoneOn
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:08:15.144829+00:00
-- url     : https://prove2.me/theorems/c3a33b2f-18b2-405a-b85d-740646266858
-- title:
--   Grid sum of an antitone function: $\sum_{j<n} f(\Delta + jh) \le f(\Delta) + h^{-1}\int_\Delta^\infty f$
-- statement:
--   **Setup.** Let $f : \mathbb{R} \to \mathbb{R}$ be antitone (non-increasing) on $[0, \infty)$ and non-negative there, let $\Delta \ge 0$, $h > 0$, assume $f$ is integrable on $(\Delta, \infty)$, and let $n$ be any natural number.
--
--   **Statement.**
--   $$\sum_{j = 0}^{n - 1} f(\Delta + j h) \;\le\; f(\Delta) + h^{-1} \int_{(\Delta,\, \infty)} f(r)\, dr.$$
--   The proof separates the $j = 0$ term and compares each remaining term with the average of $f$ over the cell $[\Delta + (j-1)h,\, \Delta + jh]$ by antitonicity, the cells being summed via adjacent-interval additivity. The bound is uniform in $n$.
--
--   **Role.** The generic sum-versus-integral comparison of the `EndsCore` module: it converts grid sums of the taper majorant $\psi$ (and of $\psi^2$) into tail integrals. Consumed by `Zeta23.PrimeSide.Sgrid_mul_le_Mnear` and by `Zeta23.PrimeSide.rho_le_majorant`, both in the error analysis of [lem:ends].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsCore.lean#L412-L464

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideA_EndsCore

open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open PrimeSide
variable {cϱ : ℝ} (p : Setting) (F : LocalFun) (ν : ℝ → ℝ)
variable {p F ν}
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem Zeta23.PrimeSide.sum_grid_le_of_antitoneOn {f : ℝ → ℝ} (hf : AntitoneOn f (Set.Ici 0))
    (h0 : ∀ x, 0 ≤ x → 0 ≤ f x) {Δ h : ℝ} (hΔ : 0 ≤ Δ) (hh : 0 < h)
    (hint : IntegrableOn f (Set.Ioi Δ)) (n : ℕ) :
    ∑ j ∈ Finset.range n, f (Δ + j * h) ≤ f Δ + h⁻¹ * ∫ r in Set.Ioi Δ, f r := by sorry
