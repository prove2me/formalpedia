-- Prove2me | Theorems.Thm_ZetaSum_aux1_phi_deriv
-- name    : ZetaSum_aux1_phi_deriv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:40:15.457482+00:00
-- url     : https://prove2.me/theorems/a4c3f20c-dedc-4c19-bf0d-b997180c6e83
-- title:
--   Derivative formula: $\dfrac{d}{dx}\, x^{-s} = -s\, x^{-(s+1)}$ for $x > 0$
-- statement:
--   Let $s \in \mathbb{C}$ with $s \neq 0$, and let $x$ be a real number with $x > 0$. Consider the complex-valued function of a real variable $t \mapsto 1/t^{s}$ (with $t$ coerced into $\mathbb{C}$). Its derivative at $x$ is given by the expected power rule:
--
--   $$\frac{d}{dx}\, \frac{1}{x^{s}} \;=\; -s \, x^{-(s+1)}.$$
--
--   This is the closed-form evaluation of the derivative whose existence is established separately: for positive real $x$ the complex power avoids the branch cut, so the usual calculus of $x^{-s}$ applies. The formula supplies the explicit integrand for the Abel-summation / integration-by-parts step producing the Euler--Maclaurin representation of the zeta partial sums $\sum_{a < n \le b} n^{-s}$ in the PNT+ project, and is reusable for any argument involving real-variable derivatives of complex power functions.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L590-L606

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

theorem ZetaSum_aux1_phi_deriv {s : ℂ} (s_ne_zero : s ≠ 0) {x : ℝ} (xpos : 0 < x) :
    deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x = (fun (x : ℝ) ↦ -s * (x : ℂ) ^ (-(s + 1))) x := by sorry
