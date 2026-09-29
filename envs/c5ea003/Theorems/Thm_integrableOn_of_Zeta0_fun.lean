-- Prove2me | Theorems.Thm_integrableOn_of_Zeta0_fun
-- name    : integrableOn_of_Zeta0_fun
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:14:02.649613+00:00
-- url     : https://prove2.me/theorems/eab5ef5d-667e-4a00-83b9-e5a2f58edcde
-- title:
--   Integrability of the Euler–Maclaurin sawtooth integrand $(\lfloor x \rfloor + \tfrac12 - x)\, x^{-(s+1)}$ on $(N, \infty)$
-- statement:
--   Let $N$ be a positive natural number and let $s \in \mathbb{C}$ with $\operatorname{Re} s > 0$. Then the function
--
--   $$x \;\longmapsto\; \Big( \lfloor x \rfloor + \tfrac{1}{2} - x \Big)\, x^{-(s+1)}$$
--
--   is Lebesgue integrable on the interval $(N, \infty)$ (with respect to Lebesgue measure on $\mathbb{R}$).
--
--   The point is that the sawtooth factor $\lfloor x \rfloor + \tfrac12 - x$ is uniformly bounded (by $\tfrac12$), while $|x^{-(s+1)}| = x^{-\operatorname{Re}(s) - 1}$ decays with exponent strictly greater than $1$, so the integral converges absolutely at infinity.
--
--   This integrability fact is a prerequisite for even defining the tail integral in the truncated zeta representation $\zeta_0$, and it underlies all subsequent manipulations of that integral — differentiation under the integral sign, integration by parts, and the resulting bounds on $\zeta$ and $\zeta'$ in the critical strip.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L776-L785

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

theorem integrableOn_of_Zeta0_fun {N : ℕ} (N_pos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    MeasureTheory.IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1))) (Ioi N)
    MeasureTheory.volume := by sorry
