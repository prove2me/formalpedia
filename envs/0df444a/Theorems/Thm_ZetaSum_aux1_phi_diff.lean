-- Prove2me | Theorems.Thm_ZetaSum_aux1_phi_diff
-- name    : ZetaSum_aux1_phi_diff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:41:09.030105+00:00
-- url     : https://prove2.me/theorems/25f7137b-b76c-4941-8c6c-c7b15c52079e
-- title:
--   Differentiability of $t \mapsto t^{-s}$ at every positive real point
-- statement:
--   Let $s \in \mathbb{C}$ and let $x$ be a real number with $x > 0$. Consider the complex-valued function of a real variable $\varphi(t) = 1/t^{s}$, where the real argument $t$ is coerced into $\mathbb{C}$ before taking the complex power. Then $\varphi$ is differentiable at $x$; formally, $\varphi$ has a derivative at $x$ equal to its Mathlib derivative:
--
--   $$\varphi \text{ has derivative } \varphi'(x) \text{ at } x, \qquad \varphi(t) = \frac{1}{t^{s}}.$$
--
--   Away from the branch point $t = 0$, the complex power $t \mapsto t^s$ is smooth in the positive real direction, so its reciprocal is differentiable. This differentiability statement (with the derivative expressed as `deriv`, whose closed form $-s\,x^{-(s+1)}$ is computed in a companion lemma) feeds into the integration-by-parts step of the Euler--Maclaurin summation formula for $\sum n^{-s}$ used throughout the PNT+ zeta-bound estimates.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L584-L588

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

theorem ZetaSum_aux1_phi_diff {s : ℂ} {x : ℝ} (xpos : 0 < x) :
    HasDerivAt (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s) x) x := by sorry
