-- Prove2me | Theorems.Thm_ZetaBnd_aux1
-- name    : ZetaBnd_aux1
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:14:53.163293+00:00
-- url     : https://prove2.me/theorems/2d3e0cf1-5188-4b00-ac95-5ab399e21835
-- title:
--   Tail integral of the sawtooth against $x^{-s-1}$: bound $\|s \int_N^{\infty} (\lfloor x\rfloor + \tfrac12 - x) x^{-s-1} dx\| \le 2|t| N^{-\sigma}/\sigma$
-- statement:
--   Let $N \ge 1$ be a natural number and let $\sigma, t$ be real numbers with $\sigma \in (0, 2]$ and $|t| \ge 2$. Write $s = \sigma + it$. Then the tail term of the Euler-Maclaurin expansion of $\zeta$ satisfies
--   $$\left\| (\sigma + it) \int_{N}^{\infty} \frac{\lfloor x \rfloor + \tfrac12 - x}{x^{s + 1}} \, dx \right\| \le \frac{2\,|t|\, N^{-\sigma}}{\sigma}.$$
--
--   Combined with the trivial bound $|s| \le \sigma + |t| \le 2|t|$ in this range and the unsigned tail estimate $\|\int_N^\infty \cdots\| \le N^{-\sigma}/\sigma$, this controls the integral remainder in the representation $\zeta(s) = \zeta_0(N, s)$. With the choice $N = \lfloor |t| \rfloor$ the right-hand side becomes $O(|t|^{1-\sigma}/\sigma)$, which is exactly the error budget allowed in the proofs of $|\zeta(\sigma+it)| \ll \log|t|$ near the $1$-line.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L842-L851

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

theorem ZetaBnd_aux1 (N : ℕ) (Npos : 1 ≤ N) {σ t : ℝ} (hσ : σ ∈ Ioc 0 2) (ht : 2 ≤ |t|) :
    ‖(σ + t * I) * ∫ x in Ioi (N : ℝ), (⌊x⌋ + 1 / 2 - x) / (x : ℂ) ^ ((σ + t * I) + 1)‖
    ≤ 2 * |t| * N ^ (-σ) / σ := by sorry
