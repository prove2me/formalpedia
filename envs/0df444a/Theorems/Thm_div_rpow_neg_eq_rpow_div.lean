-- Prove2me | Theorems.Thm_div_rpow_neg_eq_rpow_div
-- name    : div_rpow_neg_eq_rpow_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:05:26.177668+00:00
-- url     : https://prove2.me/theorems/316cfba4-e6df-4524-9dbf-a4ce7f33df3b
-- title:
--   Quotient of negative real powers as a power of the ratio: $x^{-s} / y^{-s} = (y/x)^{s}$
-- statement:
--   Let $x, y, s \in \mathbb{R}$ with $x \geq 0$ and $y \geq 0$. Then for the real power function,
--
--   $$\frac{x^{-s}}{y^{-s}} = \left(\frac{y}{x}\right)^{s}.$$
--
--   This is the companion of the identity $x^{s}/y^{s} = (y/x)^{-s}$, obtained by negating the exponent; the nonnegativity hypotheses again keep all powers within the standard real-power calculus (with the usual conventions at $0$).
--
--   It is used when comparing decaying power weights $x^{-s}$ at different scales: a ratio of two such weights collapses to a single power of the ratio of the base points, which is the form needed for monotonicity arguments in the zeta tail estimates.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L25-L27

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

theorem div_rpow_neg_eq_rpow_div {x y s : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ (-s) / y ^ (-s) = (y / x) ^ s := by sorry
