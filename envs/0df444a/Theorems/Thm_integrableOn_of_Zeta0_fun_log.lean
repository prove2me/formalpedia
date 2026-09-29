-- Prove2me | Theorems.Thm_integrableOn_of_Zeta0_fun_log
-- name    : integrableOn_of_Zeta0_fun_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:23:56.15884+00:00
-- url     : https://prove2.me/theorems/712ab192-aa65-40d3-a52d-81e588e10916
-- title:
--   Integrability of the logarithm-weighted sawtooth integrand $(\lfloor x \rfloor + \tfrac12 - x)\, x^{-(s+1)}\, (-\log x)$ on $(N, \infty)$
-- statement:
--   Let $N$ be a positive natural number and let $s \in \mathbb{C}$ with $\operatorname{Re} s > 0$. Then the function
--
--   $$x \;\longmapsto\; \Big( \lfloor x \rfloor + \tfrac{1}{2} - x \Big)\, x^{-(s+1)}\, (-\log x)$$
--
--   is Lebesgue integrable on $(N, \infty)$.
--
--   Compared with the un-weighted sawtooth integrand, the extra factor $\log x$ grows only logarithmically and is absorbed by the power decay $x^{-\operatorname{Re}(s)-1}$ with $\operatorname{Re} s > 0$, so absolute convergence at infinity persists.
--
--   This is exactly the integrand produced by differentiating the $\zeta_0$ tail integral $\int_N^{\infty} (\lfloor x \rfloor + \tfrac12 - x)\, x^{-s-1}\, dx$ with respect to $s$; its integrability is the dominating-function input that legitimizes differentiation under the integral sign and hence the holomorphy of the Euler–Maclaurin tail term of $\zeta_0$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L920-L948

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

theorem integrableOn_of_Zeta0_fun_log {N : ℕ} (Npos : 0 < N) {s : ℂ} (s_re_gt : 0 < s.re) :
    IntegrableOn (fun (x : ℝ) ↦ (⌊x⌋ + 1 / 2 - x) * (x : ℂ) ^ (-(s + 1)) * (-Real.log x)) (Ioi N)
    volume := by sorry
