-- Prove2me | Theorems.Thm_one_div_cpow_eq_cpow_neg
-- name    : one_div_cpow_eq_cpow_neg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:50:43.786527+00:00
-- url     : https://prove2.me/theorems/0082ee44-5f02-430d-b1c9-4ba6b10a27db
-- title:
--   Reciprocal of a complex power: $1/x^s = x^{-s}$
-- statement:
--   For all complex numbers $x$ and $s$, the reciprocal of the complex power $x^s$ equals the power with negated exponent:
--
--   $$\frac{1}{x^s} \;=\; x^{-s},$$
--
--   where $x^s$ denotes the principal complex power (defined via the principal logarithm, with the usual Lean conventions at $x = 0$).
--
--   This elementary rewriting lemma is used constantly in the zeta-function development to pass between the Dirichlet-series form $\sum_n 1/n^s$ and the form $\sum_n n^{-s}$, and between integrands written as $1/x^{s+1}$ and $x^{-(s+1)}$ in Mellin-type and Euler--Maclaurin integrals.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L19-L20

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

theorem one_div_cpow_eq_cpow_neg (x s : ℂ) : 1 / x ^ s = x ^ (-s) := by sorry
