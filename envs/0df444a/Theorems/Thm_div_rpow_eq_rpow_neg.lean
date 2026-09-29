-- Prove2me | Theorems.Thm_div_rpow_eq_rpow_neg
-- name    : div_rpow_eq_rpow_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:08:33.800617+00:00
-- url     : https://prove2.me/theorems/690726d0-d9a0-4ec1-9b40-2f24fb8393cf
-- title:
--   Division by a real power equals multiplication by the negated power: $a / x^s = a\, x^{-s}$
-- statement:
--   Let $a, x, s \in \mathbb{R}$ with $x \geq 0$. Then for the real power function,
--
--   $$\frac{a}{x^{s}} = a \cdot x^{-s}.$$
--
--   The hypothesis $x \geq 0$ places the identity in the regime where the real power $x^s$ obeys the usual law $x^{-s} = (x^s)^{-1}$ (the case $x = 0$ being covered by the standard junk-value conventions, under which both sides agree).
--
--   Like its complex counterpart, this is a normalization lemma: integrands and summands of analytic number theory naturally appear as quotients $a / x^{s}$, while the library's asymptotic and integrability machinery prefers products $a \cdot x^{-s}$. This lemma mediates between the two forms.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L22-L23

import Batteries.Tactic.Lemma
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.AbelSummation
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Definitions.Def_EulerMaclaurin_defs
import Definitions.Def_Fourier_defs
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs
import Definitions.Def_ZetaBounds_defs

set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

theorem div_rpow_eq_rpow_neg (a x s : ℝ) (hx : 0 ≤ x) : a / x ^ s = a * x ^ (-s) := by sorry
