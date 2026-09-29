-- Prove2me | Theorems.Thm_DerivUpperBnd_aux1
-- name    : DerivUpperBnd_aux1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:03:31.844032+00:00
-- url     : https://prove2.me/theorems/3a3030b0-607b-40f2-99de-d0e0b76c2eb5
-- title:
--   Bound on the truncated Dirichlet series of $\zeta'$: $\big\|\sum_{n \le N} \log n\, / n^{s}\big\| \le e^A C \log^2|t|$ near $\sigma = 1$
-- statement:
--   Let $A \in (0, 1/2]$, let $t$ be real with $|t| > 3$, let $C \ge 2$, and let $\sigma$ be real with
--   $$\sigma \;\ge\; 1 - \frac{A}{\log |t|}.$$
--   Set $N = \lfloor |t| \rfloor$ and $s = \sigma + it$. Then the truncated Dirichlet series for $\zeta'(s)$ satisfies
--   $$\Big\| \sum_{n = 0}^{N} \frac{-\log n}{n^{s}} \Big\| \;\le\; e^{A}\, C \,(\log |t|)^{2},$$
--   where the $n = 0$ and $n = 1$ terms vanish (as $\log n = 0$ there) and $\|\cdot\|$ is the complex modulus.
--
--   Termwise, $|n^{-s}| = n^{-\sigma} \le e^{A} n^{-1}$ for $n \le N \approx |t|$ in the stated range of $\sigma$, so the sum is dominated by $e^A \sum_{n \le |t|} \log n / n \ll e^A (\log|t|)^2$; the constant $C$ absorbs the partial-summation comparison.
--
--   This is the main-term estimate in the proof that $|\zeta'(\sigma + it)| \ll \log^2 |t|$ in the standard zero-free-region-adjacent strip $\sigma \ge 1 - A/\log|t|$ — the derivative bound that, combined with the lower bound for $|\zeta|$, controls $\zeta'/\zeta$ and drives the error term in the Prime Number Theorem.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1451-L1483

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

theorem DerivUpperBnd_aux1 {A C σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2))
    (σ_ge : 1 - A / Real.log |t| ≤ σ) (t_gt : 3 < |t|) (hC : 2 ≤ C) : let N := ⌊|t|⌋₊;
    ‖∑ n ∈ Finset.range (N + 1), -1 / (n : ℂ) ^ (σ + t * I) * (Real.log n)‖
      ≤ Real.exp A * C * (Real.log |t|) ^ 2 := by sorry
