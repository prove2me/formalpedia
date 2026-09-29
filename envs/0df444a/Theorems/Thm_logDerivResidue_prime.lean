-- Prove2me | Theorems.Thm_logDerivResidue_prime
-- name    : logDerivResidue_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:42:10.507004+00:00
-- url     : https://prove2.me/theorems/57c6d564-b850-4e11-956c-c9f8590870b8
-- title:
--   Logarithmic derivative near a simple pole (open-set version): $\frac{f'}{f} + \frac{1}{s-p} = O(1)$
-- statement:
--   Let $f : \mathbb{C} \to \mathbb{C}$, let $p \in \mathbb{C}$, and let $U \subseteq \mathbb{C}$ be an open set which is a neighborhood of $p$. Assume: (i) $f$ is nonvanishing on $U \setminus \{p\}$; (ii) $f$ is holomorphic on $U \setminus \{p\}$; and (iii) there is a constant $A \neq 0$ such that $f(s) - \dfrac{A}{s - p}$ is bounded on $U \setminus \{p\}$. Then
--
--   $$\frac{f'(s)}{f(s)} + \frac{1}{s - p} \;=\; O(1) \qquad \text{as } s \to p,\ s \neq p.$$
--
--   This is the same conclusion as the general logarithmic-derivative residue lemma, but with the additional hypothesis that $U$ is open; this is the version in which the analytic work is actually carried out (writing $f(s) = \frac{A}{s-p}(1 + g(s))$ with $g$ holomorphic and vanishing at $p$, then differentiating).
--
--   Its role is identical: applied to $\zeta$ at $s = 1$ it gives the local expansion $-\zeta'/\zeta(s) = \frac{1}{s-1} + O(1)$, the analytic origin of the main term in the Prime Number Theorem.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L268-L369

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

theorem logDerivResidue_prime {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_is_open : IsOpen U)
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by sorry
