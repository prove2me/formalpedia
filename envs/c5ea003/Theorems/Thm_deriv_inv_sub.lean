-- Prove2me | Theorems.Thm_deriv_inv_sub
-- name    : deriv_inv_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:42:28.869511+00:00
-- url     : https://prove2.me/theorems/61e8ad6b-88ef-4642-975c-c33a2fdf20a6
-- title:
--   Derivative of a simple pole: $\dfrac{d}{dz}\,(z - p)^{-1} = -\,(z-p)^{-2}$
-- statement:
--   Let $x, p \in \mathbb{C}$ with $x \neq p$. Then the reciprocal of the shifted coordinate is differentiable at $x$ with the expected derivative:
--
--   $$\frac{d}{dz}\, \frac{1}{z - p}\,\Big|_{z = x} \;=\; -\,\frac{1}{(x - p)^{2}}.$$
--
--   This is the basic derivative formula for a simple-pole term $A/(z-p)$ (with $A = 1$), valid at every point away from the pole $p$.
--
--   It is a micro-lemma in the pole-subtraction toolkit of the PNT+ zeta-bounds development: when the principal part $\frac{1}{s-1}$ of $\zeta$ is split off, the derivative of the subtracted term is needed explicitly, and this formula supplies it. Being completely generic, it is reusable in any computation involving derivatives of Möbius-type or principal-part expressions.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L195-L199

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

theorem deriv_inv_sub {x p : ℂ} (hp : x ≠ p) :
  deriv (fun z => (z - p)⁻¹) x =  -((x - p) ^ 2)⁻¹ := by sorry
