-- Prove2me | Theorems.Thm_ZetaSum_aux2a
-- name    : ZetaSum_aux2a
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:13:35.682892+00:00
-- url     : https://prove2.me/theorems/a7cd55e4-96ce-4c33-b825-8e59ccd3c61c
-- title:
--   The centered sawtooth $\lfloor x\rfloor + 1/2 - x$ is uniformly bounded
-- statement:
--   There exists a constant $C$ such that for every real number $x$,
--
--   $$\left\| \lfloor x\rfloor + \tfrac{1}{2} - x \right\| \;\le\; C,$$
--
--   where $\lfloor x\rfloor$ denotes the integer floor of $x$.
--
--   The expression $\lfloor x\rfloor + \tfrac12 - x$ is the centered (mean-zero) sawtooth function of Euler--Maclaurin summation, a periodic function taking values in $[-\tfrac12, \tfrac12]$; the lemma asserts its uniform boundedness in existential form. This boundedness is what makes the sawtooth error integrals in the truncated zeta representation absolutely convergent for $\operatorname{Re}(s) > 0$, and the lemma is reused whenever a crude uniform bound on the Euler--Maclaurin kernel suffices.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L761-L762

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

theorem ZetaSum_aux2a : ∃ C, ∀ (x : ℝ), ‖⌊x⌋ + 1 / 2 - x‖ ≤ C := by sorry
