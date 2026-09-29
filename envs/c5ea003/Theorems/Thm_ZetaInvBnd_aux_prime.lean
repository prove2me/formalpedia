-- Prove2me | Theorems.Thm_ZetaInvBnd_aux_prime
-- name    : ZetaInvBnd_aux_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:45:14.164811+00:00
-- url     : https://prove2.me/theorems/da9cf989-7021-4fc8-81ab-ec4dede0aef1
-- title:
--   Strict power comparison $\log|t| < (\log|t|)^9$ when $\log|t| > 1$
-- statement:
--   Let $t$ be a real number with $\log |t| > 1$. Then the strict inequality
--   $$\log |t| \;<\; (\log |t|)^{9}$$
--   holds.
--
--   This is the strict variant of the companion lemma $\log|t| \le (\log|t|)^9$: a real number strictly greater than $1$ is strictly smaller than its ninth power. It serves the same bookkeeping purpose in the zero-free-region argument — guaranteeing that the $A/(\log|t|)^9$-window around the $1$-line is strictly narrower than the $A/\log|t|$-region where the logarithmic upper bounds for $\zeta$ and $\zeta'$ hold — in situations where strictness of the inclusion is needed.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L2233-L2235

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

theorem ZetaInvBnd_aux_prime {t : ℝ} (logt_gt_one : 1 < Real.log |t|) : Real.log |t| < Real.log |t| ^ 9 := by sorry
