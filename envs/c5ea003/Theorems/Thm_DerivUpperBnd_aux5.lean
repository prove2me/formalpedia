-- Prove2me | Theorems.Thm_DerivUpperBnd_aux5
-- name    : DerivUpperBnd_aux5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:15:46.206189+00:00
-- url     : https://prove2.me/theorems/bb8f9c57-e5fd-4a41-a3fe-806d671ade51
-- title:
--   Tail integral of the sawtooth against $x^{-s-1}$ is bounded by $\tfrac{1}{3}\big(2|t| N^{-\sigma}/\sigma\big)$
-- statement:
--   Let $A, \sigma, t$ be real with $|t| > 3$ and $\sigma \in \big[1 - A/\log|t|,\, 2\big]$. Set $N = \lfloor |t| \rfloor$ and $s = \sigma + it$, and assume $N > 0$ and $\sigma > 1/2$. Then the sawtooth tail integral from the Euler–Maclaurin formula satisfies
--   $$\Big\| 1 \cdot \int_{N}^{\infty} \Big( \lfloor x \rfloor + \tfrac{1}{2} - x \Big)\, x^{-s-1} \, dx \Big\| \;\le\; \frac{1}{3} \cdot \frac{2\,|t|\, N^{-\sigma}}{\sigma},$$
--   where $\lfloor x \rfloor + \tfrac12 - x$ is the centered sawtooth function (bounded by $\tfrac12$ in absolute value) and the integrand is complex-valued via the principal power $x^{-s-1}$.
--
--   Pointwise, $\|(\lfloor x\rfloor + \tfrac12 - x)\, x^{-s-1}\| \le \tfrac12 x^{-\sigma-1}$, and integrating over $(N, \infty)$ gives $\tfrac{1}{2} N^{-\sigma}/\sigma$, which is well within the stated budget since $|t| > 3$.
--
--   This estimate controls one of the two tail contributions when the truncated (Euler–Maclaurin) representation of $\zeta$ is differentiated: it is packaged with the matching prefactor from the derivative computation so the pieces sum to the final $\log^2|t|$ bound on $\zeta'$ near $\sigma = 1$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1535-L1559

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

theorem DerivUpperBnd_aux5 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → 1 / 2 < σ →
    ‖1 * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1)‖ ≤
    1 / 3 * (2 * |t| * ↑N ^ (-σ) / σ) := by sorry
