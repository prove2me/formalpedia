-- Prove2me | Theorems.Thm_riemannZetaLogDerivResidue
-- name    : riemannZetaLogDerivResidue
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:45:48.060746+00:00
-- url     : https://prove2.me/theorems/e8a12106-d5fe-4eb2-9aa2-c247ea2d1f9f
-- title:
--   $-\zeta'/\zeta$ has a simple pole of residue $1$ at $s=1$: boundedness of the difference
-- statement:
--   There exists a neighborhood $U$ of $1 \in \mathbb{C}$ on which the difference between the negated logarithmic derivative of the Riemann zeta function and the model simple pole $(s-1)^{-1}$ is bounded away from the point $1$ itself: the set of values
--
--   $$\left\{\, \left\| -\frac{\zeta'(s)}{\zeta(s)} - \frac{1}{s-1} \right\| \;:\; s \in U \setminus \{1\} \,\right\}$$
--
--   is bounded above.
--
--   Equivalently, $-\zeta'/\zeta$ has a simple pole at $s = 1$ with residue $1$, and the statement records this in the quantitative form actually consumed downstream: bounded remainder on a punctured neighborhood.
--
--   The residue $1$ of $-\zeta'/\zeta$ at $s=1$ is precisely what produces the main term $x$ in the Prime Number Theorem: in the Perron/Mellin contour-shifting argument for $\psi(x) = \frac{1}{2\pi i}\int (-\zeta'/\zeta)(s) \frac{x^s}{s}\,ds$, the pole at $s = 1$ contributes the leading asymptotic, while this boundedness statement controls the error when the contour passes near $s = 1$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L476-L512

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

theorem riemannZetaLogDerivResidue :
    ∃ U ∈ 𝓝 1, BddAbove (norm ∘ (-(ζ' / ζ) - (fun s ↦ (s - 1)⁻¹)) '' (U \ {1})) := by sorry
