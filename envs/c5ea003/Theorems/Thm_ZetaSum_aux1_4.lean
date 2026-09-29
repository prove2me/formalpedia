-- Prove2me | Theorems.Thm_ZetaSum_aux1_4
-- name    : ZetaSum_aux1_4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:09:29.261295+00:00
-- url     : https://prove2.me/theorems/5df3bd82-078f-4bee-b85f-6d14826db852
-- title:
--   Norm of the sawtooth integrand: integral identity $\int_a^b \|(\lfloor x\rfloor + \tfrac12 - x)/x^{s+1}\|\,dx = \int_a^b |\lfloor x\rfloor + \tfrac12 - x| \, x^{-\mathrm{Re}(s+1)}\,dx$
-- statement:
--   Let $a, b$ be real numbers with $0 < a < b$, and let $s \in \mathbb{C}$. Then the integral of the norm of the complex sawtooth integrand equals the corresponding real integral:
--   $$\int_{a}^{b} \left\| \frac{\lfloor x \rfloor + \tfrac12 - x}{x^{s+1}} \right\| dx \;=\; \int_{a}^{b} \frac{\bigl| \lfloor x \rfloor + \tfrac12 - x \bigr|}{x^{\mathrm{Re}(s+1)}} \, dx,$$
--   where on the left $x$ is regarded as a complex number and $x^{s+1}$ is the complex power, while on the right $x^{\mathrm{Re}(s+1)}$ is a real power.
--
--   The content is the identity $\|x^{w}\| = x^{\mathrm{Re}(w)}$ for $x > 0$, applied pointwise on $[a, b]$ and integrated. This reduction from complex-norm integrals to real integrals is the bridge that lets the elementary power-integral evaluation $\int_a^b x^{-c-1} dx = (a^{-c} - b^{-c})/c$ be applied to bound the Euler-Maclaurin remainder in the truncated representation of $\zeta$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L665-L669

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

theorem ZetaSum_aux1_4 {a b : ℝ} (apos : 0 < a) (a_lt_b : a < b) {s : ℂ} :
  ∫ (x : ℝ) in a..b, ‖(↑⌊x⌋ + (1 : ℝ) / 2 - ↑x) / (x : ℂ) ^ (s + 1)‖ =
    ∫ (x : ℝ) in a..b, |⌊x⌋ + 1 / 2 - x| / x ^ (s + 1).re := by sorry
