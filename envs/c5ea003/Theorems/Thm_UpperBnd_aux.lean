-- Prove2me | Theorems.Thm_UpperBnd_aux
-- name    : UpperBnd_aux
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:00:31.877512+00:00
-- url     : https://prove2.me/theorems/70bc3618-7cc0-4dfa-ba03-bd0bdc643fec
-- title:
--   Bookkeeping bounds for the zero-free-region abscissa $\sigma \ge 1 - A/\log|t|$ with $|t| > 3$
-- statement:
--   Fix a parameter $A \in (0, \tfrac{1}{2}]$ and real numbers $\sigma, t$ with $|t| > 3$ and
--
--   $$\sigma \;\ge\; 1 - \frac{A}{\log |t|},$$
--
--   the shape of abscissa that occurs when estimating $\zeta$ and $\zeta'/\zeta$ just inside the classical zero-free region. Let $N = \lfloor |t| \rfloor$ be the integer part of $|t|$ (as a natural number).
--
--   Then all of the following elementary facts hold simultaneously:
--
--   $$0 < N, \qquad N \le |t|, \qquad 1 < \log |t|, \qquad 1 - A < \sigma, \qquad 0 < \sigma, \qquad \sigma + it \ne 1.$$
--
--   This is a pure bookkeeping lemma: it packages the routine positivity, size, and non-degeneracy facts (in particular that the point $s = \sigma + it$ is not the pole $s = 1$ of $\zeta$, since $|t| > 3$) that are needed repeatedly in the derivation of upper bounds for $|\zeta(s)|$ and $|\zeta'(s)|$ in the region $\sigma \ge 1 - A/\log|t|$. Isolating it keeps the genuinely analytic estimates on $\zeta$ free of arithmetic side conditions.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1252-L1267

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

theorem UpperBnd_aux {A σ t : ℝ} (hA : A ∈ Ioc 0 (1 / 2)) (t_gt : 3 < |t|)
    (σ_ge : 1 - A / Real.log |t| ≤ σ) :
    let N := ⌊|t|⌋₊;
    0 < N ∧ N ≤ |t| ∧ 1 < Real.log |t| ∧ 1 - A < σ ∧ 0 < σ ∧ σ + t * I ≠ 1 := by sorry
