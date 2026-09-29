-- Prove2me | Theorems.Thm_norm_zeta_product_ge_one
-- name    : norm_zeta_product_ge_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:54:42.527956+00:00
-- url     : https://prove2.me/theorems/8411ebc2-4713-442b-ad83-64c9d748c10f
-- title:
--   The Mertens $3$-$4$-$1$ inequality: $|\zeta(1{+}x)^3\, \zeta(1{+}x{+}iy)^4\, \zeta(1{+}x{+}2iy)| \ge 1$
-- statement:
--   Let $x > 0$ be a positive real number and let $y \in \mathbb{R}$. Then the classical Mertens product of Riemann zeta values on the vertical line $\operatorname{Re}(s) = 1 + x$ satisfies
--
--   $$\bigl\| \zeta(1+x)^3 \cdot \zeta(1+x+iy)^4 \cdot \zeta(1+x+2iy) \bigr\| \;\ge\; 1.$$
--
--   The proof idea (not part of the statement) rests on the trigonometric inequality $3 + 4\cos\theta + \cos 2\theta = 2(1+\cos\theta)^2 \ge 0$ applied to the Euler product/Dirichlet series of $\log \zeta$; the statement itself is the purely quantitative product bound, valid for all real $y$.
--
--   This is the key input to the nonvanishing of $\zeta$ on the line $\operatorname{Re}(s) = 1$ and, more quantitatively, to the classical zero-free region: if $\zeta(1+iy)$ were zero, the fourth-power factor would vanish to high order as $x \to 0^+$, faster than the third-power factor's pole at $s=1$ can compensate, contradicting the inequality. It is thus a cornerstone of every proof of the Prime Number Theorem via complex analysis.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1925-L1934

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

theorem norm_zeta_product_ge_one {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ‖ζ (1 + x) ^ 3 * ζ (1 + x + I * y) ^ 4 * ζ (1 + x + 2 * I * y)‖ ≥ 1 := by sorry
