-- Prove2me | Theorems.Thm_Zeta_diff_Bnd
-- name    : Zeta_diff_Bnd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:56:36.007741+00:00
-- url     : https://prove2.me/theorems/f9cf988d-e9c6-42ea-b41a-dba1ef586e3b
-- title:
--   Difference bound for zeta along horizontal segments: $\|\zeta(\sigma_2 + it) - \zeta(\sigma_1 + it)\| \le C (\log|t|)^2 (\sigma_2 - \sigma_1)$
-- statement:
--   There exist a constant $A \in (0, \tfrac{1}{2}]$ and a constant $C > 0$ such that the following holds. For all real numbers $\sigma_1, \sigma_2, t$ with $|t| > 3$,
--
--   $$1 - \frac{A}{\log|t|} \le \sigma_1, \qquad \sigma_2 \le 2, \qquad \sigma_1 < \sigma_2,$$
--
--   the values of the Riemann zeta function at the two points on the same horizontal line satisfy
--
--   $$\left\| \zeta(\sigma_2 + i t) - \zeta(\sigma_1 + i t) \right\| \;\le\; C \,(\log |t|)^{2}\, (\sigma_2 - \sigma_1).$$
--
--   This Lipschitz-type estimate follows from writing the difference as $\int_{\sigma_1}^{\sigma_2} \zeta'(\sigma + it)\, d\sigma$ and invoking the $O((\log|t|)^2)$ bound for $\zeta'$ in the same region. In the PNT+ project it is used to transfer information between nearby vertical lines inside the zero-free region — for instance to compare $\zeta$ on the $1$-line with $\zeta$ slightly to its left — a step needed for the lower bounds on $|\zeta|$ and ultimately for the contour-shifting argument in the Prime Number Theorem with error term.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L2219-L2231

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

theorem Zeta_diff_Bnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ₁ σ₂ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : 1 - A / Real.log |t| ≤ σ₁) (_ : σ₂ ≤ 2) (_ : σ₁ < σ₂),
    ‖ζ (σ₂ + t * I) - ζ (σ₁ + t * I)‖ ≤  C * Real.log |t| ^ 2 * (σ₂ - σ₁) := by sorry
