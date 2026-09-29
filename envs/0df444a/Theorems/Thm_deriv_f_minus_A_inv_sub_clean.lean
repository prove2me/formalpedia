-- Prove2me | Theorems.Thm_deriv_f_minus_A_inv_sub_clean
-- name    : deriv_f_minus_A_inv_sub_clean
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:42:54.204393+00:00
-- url     : https://prove2.me/theorems/c4713840-eef0-403d-b105-3b5daf45479e
-- title:
--   Derivative after subtracting a simple pole: $\bigl(f - \tfrac{A}{z - p}\bigr)'(x) = f'(x) + \tfrac{A}{(x-p)^2}$
-- statement:
--   Let $f : \mathbb{C} \to \mathbb{C}$ and let $A, p, x \in \mathbb{C}$. Assume $f$ is differentiable at $x$ and $x \neq p$. Then the function obtained by subtracting the simple-pole term $z \mapsto A\,(z - p)^{-1}$ from $f$ is differentiable at $x$, with derivative
--
--   $$\frac{d}{dz}\Bigl( f(z) - \frac{A}{z - p} \Bigr)\Big|_{z = x} \;=\; f'(x) \;+\; \frac{A}{(x - p)^{2}}.$$
--
--   This is the elementary computation combining linearity of the derivative with the formula $\bigl((z-p)^{-1}\bigr)' = -(z-p)^{-2}$, valid away from the pole $p$.
--
--   In the PNT+ project this identity supports the pole-subtraction analysis of $\zeta$ near $s = 1$: writing $\zeta(s) = \frac{1}{s-1} + (\text{holomorphic})$, one repeatedly needs the derivative of the regularized function $\zeta - \frac{1}{s-1}$ in terms of $\zeta'$ and the explicit $(s-1)^{-2}$ correction. The lemma is stated for a general function $f$, residue $A$, and pole location $p$, so it is reusable in any principal-part computation.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L202-L208

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

theorem deriv_f_minus_A_inv_sub_clean (f : ℂ → ℂ) (A x p : ℂ)
    (hf : DifferentiableAt ℂ f x) (hp : x ≠ p) :
    deriv (f  - (fun z ↦ A * (z - p)⁻¹)) x = deriv f x + A * ((x - p) ^ 2)⁻¹ := by sorry
