-- Prove2me | Theorems.Thm_derivative_const_plus_product
-- name    : derivative_const_plus_product
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:43:19.842115+00:00
-- url     : https://prove2.me/theorems/3c1e8b68-bbc0-4d3c-95bf-be5902b117a1
-- title:
--   Product-rule computation: $\dfrac{d}{dz}\bigl(A + g(z)(z - p)\bigr) = g'(x)(x - p) + g(x)$
-- statement:
--   Let $g : \mathbb{C} \to \mathbb{C}$ and let $A, p, x \in \mathbb{C}$, with $g$ differentiable at $x$. Consider the function $z \mapsto A + g(z)\,(z - p)$, a constant plus the product of $g$ with the linear factor $z - p$. Its derivative at $x$ is
--
--   $$\frac{d}{dz}\Bigl( A + g(z)(z - p) \Bigr)\Big|_{z = x} \;=\; g'(x)\,(x - p) \;+\; g(x).$$
--
--   This is the product rule combined with vanishing of the constant's derivative and $\frac{d}{dz}(z - p) = 1$, packaged for the specific shape that arises when a function with a simple pole at $p$ is written in the form $\frac{A + g(z)(z-p)}{z - p}$: the numerator's derivative is exactly the expression above.
--
--   In the PNT+ zeta-bounds development this feeds the local analysis of $\zeta$ near its pole at $s = 1$, where $\zeta(s)(s-1) = 1 + (\text{holomorphic})(s-1)$-type factorizations are differentiated. The lemma is fully generic in $g$, $A$, and $p$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L190-L193

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

theorem derivative_const_plus_product {g : ℂ → ℂ} (A p x : ℂ) (hg : DifferentiableAt ℂ g x) :
    deriv ((fun _ ↦ A) + g * fun s ↦ s - p) x = deriv g x * (x - p) + g x := by sorry
