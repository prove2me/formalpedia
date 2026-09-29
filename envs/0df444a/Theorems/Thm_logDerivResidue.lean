-- Prove2me | Theorems.Thm_logDerivResidue
-- name    : logDerivResidue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:44:03.573224+00:00
-- url     : https://prove2.me/theorems/7516a93a-d794-49e8-af3e-ea11591ff164
-- title:
--   Logarithmic derivative near a simple pole: $\frac{f'}{f} + \frac{1}{s - p} = O(1)$ as $s \to p$
-- statement:
--   Let $f : \mathbb{C} \to \mathbb{C}$, let $p \in \mathbb{C}$, and let $U \subseteq \mathbb{C}$ be a neighborhood of $p$. Assume: (i) $f$ is nonvanishing on $U \setminus \{p\}$; (ii) $f$ is holomorphic on $U \setminus \{p\}$; and (iii) there is a nonzero constant $A \in \mathbb{C}$ such that the difference $f(s) - \dfrac{A}{s - p}$ is bounded on $U \setminus \{p\}$ — i.e. $f$ has a simple pole at $p$ with residue $A \neq 0$, up to a bounded error. Then the logarithmic derivative of $f$ satisfies
--
--   $$\frac{f'(s)}{f(s)} + \frac{1}{s - p} \;=\; O(1) \qquad \text{as } s \to p,\ s \neq p,$$
--
--   where the asymptotic is with respect to the punctured neighborhood filter at $p$.
--
--   In words: a function behaving like $A/(s-p)$ near $p$ has logarithmic derivative behaving like $-1/(s-p)$, with a bounded correction. This is the abstract residue computation applied in the Prime Number Theorem to $f = \zeta$ at $p = 1$: it yields $-\zeta'/\zeta(s) = \frac{1}{s-1} + O(1)$ near the pole, which is the source of the main term $x$ in the asymptotic for $\psi(x)$. Stated for a general $f$, it is reusable for any meromorphic function with a simple pole or zero.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L372-L391

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

theorem logDerivResidue {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by sorry
