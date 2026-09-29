-- Prove2me | Theorems.Thm_riemannZetaLogDerivResidueBigO
-- name    : riemannZetaLogDerivResidueBigO
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:05:51.959428+00:00
-- url     : https://prove2.me/theorems/aa373323-21d4-4da5-84f3-c00542d74774
-- title:
--   Big-$O$ form of the simple pole of $-\zeta'/\zeta$ at $s=1$
-- statement:
--   The difference between $-\zeta'/\zeta$ and the model simple pole $(z-1)^{-1}$ is bounded near $s = 1$, expressed in asymptotic notation: along the punctured-neighborhood filter at $1$ (the filter $\mathcal{N}(1) \sqcap \text{principal}(\{1\}^{c})$, i.e. $z \to 1$ with $z \neq 1$),
--
--   $$-\frac{\zeta'(z)}{\zeta(z)} - \frac{1}{z-1} \;=\; O(1).$$
--
--   That is, the remainder after subtracting the principal part of the pole stays bounded as $z \to 1$, $z \ne 1$.
--
--   This is the filter/`IsBigO` packaging of the residue statement for $-\zeta'/\zeta$ at $s = 1$: it interfaces directly with Mathlib's asymptotic calculus, so that in the contour-integration estimates for the smoothed Chebyshev function one can manipulate the pole of the integrand by adding and subtracting $(z-1)^{-1}$ and absorb the difference into $O(1)$ error terms.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L515-L519

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

theorem riemannZetaLogDerivResidueBigO :
    (-ζ' / ζ - fun z ↦ (z - 1)⁻¹) =O[nhdsWithin 1 {1}ᶜ] (1 : ℂ → ℂ) := by sorry
