-- Prove2me | Theorems.Thm_ZetaUpperBnd
-- name    : ZetaUpperBnd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:51:12.159609+00:00
-- url     : https://prove2.me/theorems/22837412-bc95-47e2-806d-b3f42e1af557
-- title:
--   Logarithmic upper bound for $\zeta$ near the $1$-line: $\|\zeta(\sigma + it)\| \le C \log|t|$ in a $1/\log|t|$-neighbourhood
-- statement:
--   There exist a constant $A \in (0, \tfrac{1}{2}]$ and a constant $C > 0$ such that for all real $\sigma$ and $t$ with $|t| > 3$ and
--
--   $$1 - \frac{A}{\log|t|} \;\le\; \sigma \;\le\; 2,$$
--
--   the Riemann zeta function satisfies the bound
--
--   $$\left\| \zeta(\sigma + i t) \right\| \;\le\; C \log |t|.$$
--
--   This is the classical upper estimate for $\zeta$ in a region extending slightly to the left of the line $\operatorname{Re}(s) = 1$, with width shrinking like $1/\log|t|$. It is proved from the truncated Euler--Maclaurin representation of $\zeta$ with cutoff $N \approx |t|$, and it is one of the two analytic inputs (together with the corresponding bounds for $\zeta'$ and the zero-free region) that drive the quantitative Perron/contour-integration argument for the Prime Number Theorem with an error term in the PNT+ project.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1405-L1415

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

theorem ZetaUpperBnd :
    ∃ (A : ℝ) (_ : A ∈ Ioc 0 (1 / 2)) (C : ℝ) (_ : 0 < C), ∀ (σ : ℝ) (t : ℝ) (_ : 3 < |t|)
    (_ : σ ∈ Icc (1 - A / Real.log |t|) 2), ‖ζ (σ + t * I)‖ ≤ C * Real.log |t| := by sorry
