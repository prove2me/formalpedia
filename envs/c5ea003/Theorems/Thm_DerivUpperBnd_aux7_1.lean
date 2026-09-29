-- Prove2me | Theorems.Thm_DerivUpperBnd_aux7_1
-- name    : DerivUpperBnd_aux7_1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:16:36.101478+00:00
-- url     : https://prove2.me/theorems/7a3e6c88-4583-4ff0-9e09-ce2abac1d33c
-- title:
--   Modulus identity for the logarithmic sawtooth integrand: $\|(\lfloor x\rfloor + \tfrac12 - x)\, x^{-s-1}(-\log x)\| = |\lfloor x\rfloor + \tfrac12 - x|\, x^{-\sigma-1} \log x$
-- statement:
--   Let $x \ge 1$ and $\sigma, t$ be real, and set $s = \sigma + it$. Then the complex modulus of the logarithmic sawtooth integrand factors exactly:
--   $$\Big\| \Big( \lfloor x \rfloor + \tfrac{1}{2} - x \Big)\, x^{-s-1}\, (-\log x) \Big\| \;=\; \Big| \lfloor x \rfloor + \tfrac{1}{2} - x \Big| \; x^{-\sigma-1}\, \log x,$$
--   where on the left the sawtooth factor and $-\log x$ are real numbers coerced into $\mathbb{C}$ and $x^{-s-1}$ is the principal complex power.
--
--   The identity combines multiplicativity of the modulus with the fact that for a positive real base $|x^{-s-1}| = x^{-\mathrm{Re}(s)-1} = x^{-\sigma-1}$, and that $\log x \ge 0$ for $x \ge 1$ so $|-\log x| = \log x$.
--
--   It is the pointwise normalization step that turns the complex tail integral appearing in the $\zeta'$ Euler–Maclaurin estimate into a purely real integral, ready for the elementary comparison $|\lfloor x\rfloor + \tfrac12 - x| \le \tfrac12 \le 1$ and explicit integration.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1575-L1581

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

theorem DerivUpperBnd_aux7_1 {x σ t : ℝ} (hx : 1 ≤ x) :
    let s := ↑σ + ↑t * I;
    ‖(↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ = |(↑⌊x⌋ + 1 / 2 - x)| * x ^ (-σ - 1) * x.log := by sorry
