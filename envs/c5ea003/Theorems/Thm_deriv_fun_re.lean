-- Prove2me | Theorems.Thm_deriv_fun_re
-- name    : deriv_fun_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:55:45.822144+00:00
-- url     : https://prove2.me/theorems/647acb3d-155b-4126-abf9-35c2dc8083a7
-- title:
--   Derivative in the real direction along a horizontal line: $\dfrac{d}{d\sigma} f(\sigma + it) = f'(\sigma + it)$
-- statement:
--   Let $t \in \mathbb{R}$ and let $f : \mathbb{C} \to \mathbb{C}$ be complex-differentiable at every point $\sigma + it$ of the horizontal line at height $t$ (i.e. for all real $\sigma$). Then the real-variable derivative of the restricted function $\sigma \mapsto f(\sigma + it)$ is, as a function of $\sigma$, the restriction of the complex derivative:
--
--   $$\frac{d}{d\sigma}\, f(\sigma + i t) \;=\; f'(\sigma + i t) \qquad \text{for all } \sigma \in \mathbb{R}.$$
--
--   This is the horizontal-direction instance of the general principle that restricting a complex-differentiable function to a real line respects derivatives (the affine parametrization $\sigma \mapsto \sigma + it$ has derivative $1$). It is stated as an equality of functions of $\sigma$, ready for use inside interval integrals.
--
--   In the PNT+ zeta-bounds development, this lemma justifies applying the one-variable fundamental theorem of calculus to $\sigma \mapsto \zeta(\sigma + it)$, yielding the identity $\int_{\sigma_1}^{\sigma_2} \zeta'(\sigma + it)\,d\sigma = \zeta(\sigma_2 + it) - \zeta(\sigma_1 + it)$ that converts $\zeta'$ bounds into difference bounds for $\zeta$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L2185-L2191

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
set_option backward.isDefEq.respectTransparency false

theorem deriv_fun_re {t : ℝ} {f : ℂ → ℂ} (diff : ∀ (σ : ℝ), DifferentiableAt ℂ f (↑σ + ↑t * I)) :
    (deriv fun {σ₂ : ℝ} ↦ f (σ₂ + t * I)) = fun (σ : ℝ) ↦ deriv f (σ + t * I) := by sorry
