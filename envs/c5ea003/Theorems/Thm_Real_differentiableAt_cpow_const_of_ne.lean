-- Prove2me | Theorems.Thm_Real_differentiableAt_cpow_const_of_ne
-- name    : Real.differentiableAt_cpow_const_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:26:35.178455+00:00
-- url     : https://prove2.me/theorems/33432e0d-b761-4be4-955e-927937f5fcab
-- title:
--   Real differentiability of $x\mapsto x^{s}$ (complex exponent) at any $x>0$
-- statement:
--   Let $s\in\mathbb{C}$ and let $x\in\mathbb{R}$ with $x>0$. Then the function
--
--   $$x \;\longmapsto\; x^{s} \quad (\text{the complex power } (x:\mathbb{C})^{s})$$
--
--   viewed as a map $\mathbb{R}\to\mathbb{C}$, is differentiable (over $\mathbb{R}$) at the point $x$.
--
--   For $x>0$ the complex power is given by $x^s=\exp(s\log x)$ with the standard real logarithm, a composition of real-differentiable maps; the positivity hypothesis keeps $x$ away from the branch point at $0$ where the complex power function is badly behaved.
--
--   This is a small regularity lemma supporting the contour and Mellin manipulations of the development: integrands of the form $x^{s-1}f(x)$ or $X^{s}$ must be differentiated in the real variable $x$ (for integration by parts, or for verifying hypotheses of differentiation-under-the-integral and fundamental-theorem-of-calculus steps), and this lemma discharges the pointwise differentiability obligation.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L537-L540

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

local notation (name := riemannzeta) "ζ" => riemannZeta
local notation (name := derivriemannzeta) "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation (name := riemannzeta0) "ζ₀" => riemannZeta0

theorem Real.differentiableAt_cpow_const_of_ne (s : ℂ) {x : ℝ} (xpos : 0 < x) :
    DifferentiableAt ℝ (fun (x : ℝ) ↦ (x : ℂ) ^ s) x := by sorry
