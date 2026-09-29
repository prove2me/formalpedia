-- Prove2me | Theorems.Thm_DerivUpperBnd_aux7
-- name    : DerivUpperBnd_aux7
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:20:50.426347+00:00
-- url     : https://prove2.me/theorems/896ff799-abed-46af-bdb3-e2ef48d4592b
-- title:
--   Logarithmic sawtooth tail integral is bounded by $6|t| N^{-\sigma} \log|t| / \sigma$
-- statement:
--   Let $A, \sigma, t$ be real with $|t| > 3$ and $\sigma \in \big[1 - A/\log|t|,\, 2\big]$. Set $N = \lfloor |t| \rfloor$ and $s = \sigma + it$, and assume $N > 0$, $N \le |t|$, $s \neq 1$, and $\sigma > 1/2$. Then the tail integral produced by differentiating the sawtooth term of the truncated zeta representation satisfies
--   $$\Big\| s \int_{N}^{\infty} \Big( \lfloor x \rfloor + \tfrac{1}{2} - x \Big)\, x^{-s-1} \,(-\log x)\, dx \Big\| \;\le\; \frac{6\,|t|\, N^{-\sigma}}{\sigma}\, \log |t|,$$
--   where $\lfloor x \rfloor + \tfrac12 - x$ is the centered sawtooth (of absolute value at most $\tfrac12$).
--
--   The integrand is dominated pointwise by $\tfrac12 x^{-\sigma-1} \log x$, whose integral over $(N,\infty)$ is of size $N^{-\sigma}(\log N + 1/\sigma)/\sigma$-type; combined with $|s| \le \sigma + |t| \ll |t|$ this yields the stated bound with explicit constant $6$.
--
--   This is the most involved of the tail estimates for the derivative of the truncated Euler–Maclaurin representation of $\zeta$: together with the companion bound reducing $2|t|N^{-\sigma}/\sigma$ to $O(e^A)$, it shows the differentiated tail contributes only $O(e^A \log|t|)$ to $\zeta'(\sigma + it)$ in the strip $\sigma \ge 1 - A/\log|t|$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1665-L1711

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
open MeasureTheory

theorem DerivUpperBnd_aux7 {A σ t : ℝ} (t_gt : 3 < |t|) (hσ : σ ∈ Icc (1 - A / |t|.log) 2) :
    let N := ⌊|t|⌋₊;
    let s := ↑σ + ↑t * I;
    0 < N → ↑N ≤ |t| → s ≠ 1 → 1 / 2 < σ →
    ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (↑⌊x⌋ + 1 / 2 - ↑x) * (x : ℂ) ^ (-s - 1) * -↑x.log‖ ≤
      6 * |t| * ↑N ^ (-σ) / σ * |t|.log := by sorry
