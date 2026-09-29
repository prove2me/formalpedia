-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_setIntegral_Iio_comp_sub_left
-- name    : Zeta23.PrimeSide.setIntegral_Iio_comp_sub_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:16:55.972766+00:00
-- url     : https://prove2.me/theorems/85f9eae8-35ee-4424-9304-fb1d3ebc3bf4
-- title:
--   Change of variables $\Delta = T - \tau$ on $(-\infty, T)$
-- statement:
--   **Statement.** For every function $f : \mathbb{R} \to \mathbb{R}$ and every $T \in \mathbb{R}$,
--   $$\int_{(-\infty,\, T)} f(T - \tau)\, d\tau = \int_{(0,\, \infty)} f(\Delta)\, d\Delta,$$
--   i.e. the substitution $\Delta = T - \tau$ maps the half-line to the left of $T$ onto the positive half-line, preserving Lebesgue measure. The identity holds for arbitrary $f$ (Bochner integrals of non-integrable functions are $0$ on both sides under Lean's conventions, since the substitution is a measure-preserving bijection).
--
--   **Role.** A leaf change-of-variables lemma used in `Zeta23.PrimeSide.nu_grid_bound_raw` (module `EndsNu`) to reduce integrals of the density $\nu$ against shifted taper majorants over the left tail $\tau < T$ to standardized integrals over $(0,\infty)$, in the $\mathcal{E}_2$ tail estimates of [lem:ends].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsNu.lean#L207-L220

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
import Definitions.Def_Zeta23_PrimeSideA_EndsNu

set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem Zeta23.PrimeSide.setIntegral_Iio_comp_sub_left (f : ℝ → ℝ) (T : ℝ) :
    ∫ τ in Iio T, f (T - τ) = ∫ Δ in Ioi 0, f Δ := by sorry
