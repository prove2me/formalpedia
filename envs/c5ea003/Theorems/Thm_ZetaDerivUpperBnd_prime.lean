-- Prove2me | Theorems.Thm_ZetaDerivUpperBnd_prime
-- name    : ZetaDerivUpperBnd_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:43:27.534732+00:00
-- url     : https://prove2.me/theorems/f1c8e47d-b288-457e-a1f8-66d6ef5661a7
-- title:
--   Explicit six-term Euler-Maclaurin bound for $\zeta'$: total $\le 59\, e^A \log^2|t|$ near the $1$-line
-- statement:
--   Let $A, \sigma, t$ be real numbers with $A \in (0, \tfrac12]$, $|t| > 3$, and
--   $$\sigma \in \left[ 1 - \frac{A}{\log |t|},\; 2 \right].$$
--   Set $C = 59\, e^{A}$, $N = \lfloor |t| \rfloor$, and $s = \sigma + it$. Then the six terms obtained by differentiating the truncated Euler-Maclaurin representation of $\zeta$ term by term satisfy, in aggregate,
--   $$\Bigl\| \sum_{n=0}^{N} \frac{-\log n}{n^{s}} \Bigr\| + \Bigl\| \frac{-N^{1-s}}{(1-s)^{2}} \Bigr\| + \Bigl\| \frac{(\log N)\, N^{1-s}}{1-s} \Bigr\| + \Bigl\| \frac{(\log N)\, N^{-s}}{2} \Bigr\| + \Bigl\| \int_{N}^{\infty} \bigl(\lfloor x \rfloor + \tfrac12 - x\bigr) x^{-s-1} dx \Bigr\| + \Bigl\| s \int_{N}^{\infty} \bigl(\lfloor x \rfloor + \tfrac12 - x\bigr) x^{-s-1} (-\log x)\, dx \Bigr\| \;\le\; C\, (\log |t|)^{2}.$$
--
--   This is the fully explicit, term-by-term version of the estimate $\|\zeta'(\sigma+it)\| \ll \log^2|t|$ in the region $\sigma \ge 1 - A/\log|t|$: each displayed norm is one summand of $\zeta_0'(N, s)$ (the derivative of the truncated zeta representation with cutoff $N = \lfloor |t|\rfloor$), and the constant $59\, e^A$ is an explicit bookkeeping of all six contributions. The existential form of the $\zeta'$ upper bound is obtained directly from this statement together with the identity $\zeta = \zeta_0(N, \cdot)$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1714-L1802

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

theorem ZetaDerivUpperBnd_prime {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * 59;
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ s * (Real.log n)‖ +
      ‖-(N : ℂ) ^ (1 - s) / (1 - s) ^ 2‖ +
      ‖(Real.log N) * (N : ℂ) ^ (1 - s) / (1 - s)‖ +
      ‖(Real.log N) * (N : ℂ) ^ (-s) / 2‖ +
      ‖(1 * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1))‖ +
      ‖s * ∫ (x : ℝ) in Ioi (N : ℝ),
        (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-s - 1) * -(Real.log x)‖
        ≤ C * Real.log |t| ^ 2 := by sorry
