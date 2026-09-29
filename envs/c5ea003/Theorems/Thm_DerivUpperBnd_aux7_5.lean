-- Prove2me | Theorems.Thm_DerivUpperBnd_aux7_5
-- name    : DerivUpperBnd_aux7_5
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:19:49.780453+00:00
-- url     : https://prove2.me/theorems/95b9e5f9-7577-4e8a-ac2b-5efcd0d1ab7f
-- title:
--   Integrability of the sawtooth-weighted integrand $|\lfloor x\rfloor + \tfrac12 - x|\, x^{-\sigma-1}\log x$
-- statement:
--   Let $a, \sigma \in \mathbb{R}$ with $\sigma > 0$ and $a \geq 1$. Then the function
--   $$x \mapsto \left|\lfloor x \rfloor + \tfrac{1}{2} - x\right| \cdot x^{-\sigma-1} \log x$$
--   is Lebesgue integrable on $(a, \infty)$.
--
--   The weight $\lfloor x \rfloor + \tfrac12 - x$ is the (shifted) sawtooth function appearing in the first-order Euler-Maclaurin summation formula; it is bounded by $\tfrac12$ in absolute value, so integrability reduces to that of the majorant $x^{-\sigma-1}\log x$, which converges since $\sigma > 0$.
--
--   In the PNT+ project this lemma justifies the absolute convergence of the Euler-Maclaurin error integral that appears when differentiating the truncated zeta representation $\zeta_0$, en route to explicit upper bounds for $|\zeta'(s)|$ in the critical strip. It is reusable for any Euler-Maclaurin-type remainder with a power-times-log kernel.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1644-L1653

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

theorem DerivUpperBnd_aux7_5 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ |(↑⌊x⌋ + (1 : ℝ) / 2 - x)| * x ^ (-σ - 1) * Real.log x)
      (Ioi a) volume := by sorry
