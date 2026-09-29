-- Prove2me | Theorems.Thm_ZetaSum_aux1_deriv_phi_cont
-- name    : ZetaSum_aux1_deriv_phi_cont
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:40:42.253517+00:00
-- url     : https://prove2.me/theorems/aace8e89-7cf3-4861-a237-ec3cc383f76b
-- title:
--   Continuity of the derivative of $t \mapsto t^{-s}$ on a positive interval
-- statement:
--   Let $s \in \mathbb{C}$ with $s \neq 0$, and let $a, b$ be natural numbers with $0 < a < b$. Consider the complex-valued function of a real variable $\varphi(t) = 1/t^{s}$ (the real number $t$ being coerced into $\mathbb{C}$ before raising to the complex power $s$). Then the derivative of $\varphi$,
--
--   $$t \;\longmapsto\; \varphi'(t) = \frac{d}{dt}\, \frac{1}{t^{s}},$$
--
--   is continuous on the closed interval $[a, b]$ (formally, on the unordered closed interval $[[a,b]]$).
--
--   Since $[a,b]$ lies in the positive reals, the derivative equals $-s\, t^{-(s+1)}$ there, which is manifestly continuous; the lemma packages this regularity in the form required by the integration-by-parts (Abel summation) step that produces the Euler--Maclaurin formula for partial sums $\sum_{a < n \le b} n^{-s}$ in the PNT+ zeta-bounds development.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L608-L613

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

theorem ZetaSum_aux1_deriv_phi_cont {s : ℂ} (s_ne_zero : s ≠ 0) {a b : ℕ} (ha : a ∈ Ioo 0 b) :
    ContinuousOn (deriv (fun (t : ℝ) ↦ 1 / (t : ℂ) ^ s)) [[a, b]] := by sorry
