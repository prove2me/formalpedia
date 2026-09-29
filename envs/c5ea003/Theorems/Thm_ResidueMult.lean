-- Prove2me | Theorems.Thm_ResidueMult
-- name    : ResidueMult
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:03:59.930254+00:00
-- url     : https://prove2.me/theorems/80a8f01c-528b-47e8-9557-d18a300eb986
-- title:
--   Simple-pole principal parts multiply: if $f\sim \frac{A}{s-p}$ and $g$ is holomorphic, then $fg\sim \frac{A\,g(p)}{s-p}$
-- statement:
--   Let $f,g\colon\mathbb{C}\to\mathbb{C}$, let $p\in\mathbb{C}$, and let $U$ be a neighborhood of $p$ on which $g$ is holomorphic. Suppose $f$ has a simple pole at $p$ with residue $A$ in the bounded-remainder sense:
--
--   $$f(s) - \frac{A}{s-p} \;=\; O(1) \qquad (s\to p,\ s\ne p).$$
--
--   Then the product $fg$ has a simple pole at $p$ with residue $A\,g(p)$ in the same sense:
--
--   $$f(s)\,g(s) - \frac{A\,g(p)}{s-p} \;=\; O(1) \qquad (s\to p,\ s\ne p).$$
--
--   The proof idea is the splitting $fg - \frac{A g(p)}{s-p} = \bigl(f-\frac{A}{s-p}\bigr)g + A\,\frac{g(s)-g(p)}{s-p}$, where the first term is bounded because $g$ is bounded near $p$, and the second is bounded because the difference quotient of the holomorphic $g$ converges to $g'(p)$.
--
--   This is the multiplicativity rule for residues of simple poles in the lightweight "big-O principal part" formalism used by this development's rectangle residue calculus. It is what transports the residue of $-\zeta'/\zeta$ at $s=1$ (residue $1$) onto the full Perron integrand $-\frac{\zeta'}{\zeta}(s)\,\mathcal{M}(\widetilde{1_\varepsilon})(s)\,X^{s}$, whose residue at $s=1$ becomes the main term $\mathcal{M}(\widetilde{1_\varepsilon})(1)\,X$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L424-L473

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

theorem ResidueMult {f g : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (g_holc : HolomorphicOn g U) (U_in_nhds : U ∈ 𝓝 p) {A : ℂ}
    (f_near_p : (f - (fun s ↦ A * (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    (f * g - (fun s ↦ A * g p * (s - p)⁻¹)) =O[𝓝[≠] p] (1 : ℂ → ℂ) := by sorry
