-- Prove2me | Theorems.Thm_div_cpow_eq_cpow_neg
-- name    : div_cpow_eq_cpow_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:15:20.864695+00:00
-- url     : https://prove2.me/theorems/be4966ae-1b30-4d65-bb98-30d03e114c5c
-- title:
--   Division by a complex power equals multiplication by the negated power: $a / x^s = a\, x^{-s}$
-- statement:
--   For all complex numbers $a, x, s \in \mathbb{C}$,
--
--   $$\frac{a}{x^{s}} = a \cdot x^{-s},$$
--
--   where $x^s$ denotes the principal-branch complex power. The identity holds unconditionally, with the degenerate cases (such as $x = 0$) handled by the standard conventions for the complex power function and for division by zero (both sides then equal $0$ when they should).
--
--   This is a small algebraic rewriting lemma used constantly when manipulating Dirichlet series and Mellin-type integrands, where terms of the form $a / n^{s}$ must be rewritten as $a \cdot n^{-s}$ to match the shape expected by summability and integrability lemmas.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L16-L17

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

theorem div_cpow_eq_cpow_neg (a x s : ℂ) : a / x ^ s = a * x ^ (-s) := by sorry
