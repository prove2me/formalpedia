-- Prove2me | Theorems.Thm_sum_eq_int_deriv
-- name    : sum_eq_int_deriv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:27:21.24844+00:00
-- url     : https://prove2.me/theorems/e9b30ff4-7cfa-4d51-90cd-bef0f2c2ade3
-- title:
--   First-order Euler–Maclaurin summation formula on an interval $[a,b]$
-- statement:
--   Let $\varphi : \mathbb{R} \to \mathbb{C}$ and let $0 \le a < b$ be real numbers. Assume $\varphi$ is differentiable on the closed interval $[a, b]$ (at every point $x \in [a,b]$ it has derivative $\varphi'(x)$), and that $\varphi'$ is continuous on $[a, b]$. Then the sum of $\varphi$ over the integers $n$ with $\lfloor a \rfloor < n \le \lfloor b \rfloor$ (natural-number floors) satisfies
--
--   $$\sum_{\lfloor a \rfloor < n \le \lfloor b \rfloor} \varphi(n) \;=\; \int_a^b \varphi(x)\,dx \;+\; \left( \lfloor b \rfloor + \tfrac12 - b \right) \varphi(b) \;-\; \left( \lfloor a \rfloor + \tfrac12 - a \right) \varphi(a) \;-\; \int_a^b \left( \lfloor x \rfloor + \tfrac12 - x \right) \varphi'(x)\,dx.$$
--
--   This is the Euler--Maclaurin formula to first order (equivalently, Abel summation with the sawtooth weight $\lfloor x \rfloor + \tfrac12 - x$): it converts a sum over integers into an integral plus boundary corrections plus a sawtooth-weighted integral of the derivative.
--
--   It is the engine behind the truncated zeta representation $\zeta_0$: applying it to $\varphi(x) = x^{-s}$ over dyadic-type ranges and letting $b \to \infty$ produces the analytic continuation of $\zeta$ to $\operatorname{Re}(s) > 0$ together with the explicit error terms from which all the PNT+ growth bounds on $\zeta$ and $\zeta'$ in the critical strip are derived.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L547-L566

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

theorem sum_eq_int_deriv {φ : ℝ → ℂ} {a b : ℝ} (apos : 0 ≤ a) (a_lt_b : a < b)
    (φDiff : ∀ x ∈ [[a, b]], HasDerivAt φ (deriv φ x) x)
    (derivφCont : ContinuousOn (deriv φ) [[a, b]]) :
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, φ n =
      (∫ x in a..b, φ x) + (⌊b⌋₊ + 1 / 2 - b) * φ b - (⌊a⌋₊ + 1 / 2 - a) * φ a
        - ∫ x in a..b, (⌊x⌋ + 1 / 2 - x) * deriv φ x := by sorry
