-- Prove2me | Theorems.Thm_Zeta23_PrimeSide_setIntegral_Ioi_comp_sub_right
-- name    : Zeta23.PrimeSide.setIntegral_Ioi_comp_sub_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T21:17:14.029446+00:00
-- url     : https://prove2.me/theorems/4851ea5e-141b-4431-a54a-6e3c9de6e470
-- title:
--   Change of variables $\Delta = \tau - c$ on $(c, \infty)$
-- statement:
--   **Statement.** For every function $f : \mathbb{R} \to \mathbb{R}$ and every $c \in \mathbb{R}$,
--   $$\int_{(c,\, \infty)} f(\tau - c)\, d\tau = \int_{(0,\, \infty)} f(\Delta)\, d\Delta,$$
--   i.e. the substitution $\Delta = \tau - c$ translates the half-line $(c, \infty)$ onto $(0, \infty)$, preserving Lebesgue measure. The identity holds for arbitrary $f$ under Lean's Bochner-integral conventions, since translation is measure-preserving.
--
--   **Role.** The right-tail companion of `setIntegral_Iio_comp_sub_left`; both feed `Zeta23.PrimeSide.nu_grid_bound_raw` (module `EndsNu`), which standardizes tail integrals of the density $\nu$ against shifted taper majorants in the $\mathcal{E}_2$ estimates of [lem:ends].
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/PrimeSideA/EndsNu.lean#L222-L235

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

theorem Zeta23.PrimeSide.setIntegral_Ioi_comp_sub_right (f : ℝ → ℝ) (c : ℝ) :
    ∫ τ in Ioi c, f (τ - c) = ∫ Δ in Ioi 0, f Δ := by sorry
