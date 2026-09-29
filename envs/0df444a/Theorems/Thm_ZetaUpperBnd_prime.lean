-- Prove2me | Theorems.Thm_ZetaUpperBnd_prime
-- name    : ZetaUpperBnd_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:43:53.967289+00:00
-- url     : https://prove2.me/theorems/7b0c65eb-a3a1-4164-af1e-9131b5f03a1b
-- title:
--   Explicit four-term Euler--Maclaurin bound for $\zeta(\sigma + it)$: each piece totals at most $21 e^{A} \log|t|$
-- statement:
--   Let $A \in (0, \tfrac{1}{2}]$, and let $\sigma, t$ be real numbers with $|t| > 3$ and $1 - A/\log|t| \le \sigma \le 2$. Set $C = e^{A}(5 + 8 \cdot 2) = 21\,e^{A}$, let $N = \lfloor |t| \rfloor$ (as a natural number), and write $s = \sigma + i t$. Then the four constituents of the truncated Euler--Maclaurin representation of $\zeta(s)$ satisfy the combined bound
--
--   $$\Bigl\| \sum_{n=0}^{N} \frac{1}{n^{s}} \Bigr\| \;+\; \Bigl\| \frac{N^{1-s}}{1-s} \Bigr\| \;+\; \Bigl\| \frac{N^{-s}}{2} \Bigr\| \;+\; \Bigl\| s \int_{N}^{\infty} \frac{\lfloor x\rfloor + \tfrac{1}{2} - x}{x^{\,s+1}}\, dx \Bigr\| \;\le\; C \log |t|,$$
--
--   where $\lfloor x\rfloor$ is the floor function and the integral runs over the ray $(N, \infty)$.
--
--   This is the fully explicit, quantitative core of the zeta upper bound: choosing the cutoff $N \approx |t|$ makes the finite Dirichlet sum contribute $O(e^{A}\log|t|)$ while the three correction terms stay bounded. Summing the four norms dominates $\|\zeta(s)\|$ itself via the truncated representation, yielding the $C\log|t|$ estimate for $\zeta$ near the $1$-line used throughout the PNT+ error-term analysis.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1364-L1403

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

theorem ZetaUpperBnd_prime {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (hσ : σ ∈ Icc (1 - A / Real.log |t|) 2) :
    let C := Real.exp A * (5 + 8 * 2); -- the 2 comes from ZetaBnd_aux1
    let N := ⌊|t|⌋₊;
    let s := σ + t * I;
    ‖∑ n ∈ Finset.range (N + 1), 1 / (n : ℂ) ^ s‖ + ‖(N : ℂ) ^ (1 - s) / (1 - s)‖
    + ‖(N : ℂ) ^ (-s) / 2‖
    + ‖s * ∫ (x : ℝ) in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ (s + 1)‖
    ≤ C * Real.log |t| := by sorry
