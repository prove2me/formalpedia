-- Prove2me | Theorems.Thm_HasDerivAt_cpow_over_var
-- name    : HasDerivAt_cpow_over_var
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:21:50.743023+00:00
-- url     : https://prove2.me/theorems/39b2cf60-fddf-401a-9a71-7289cccd7d43
-- title:
--   Derivative of $z \mapsto -N^{z}/z$
-- statement:
--   Let $N$ be a natural number and let $z \in \mathbb{C}$ with $z \neq 0$. Then the function $w \mapsto -N^{w}/w$ (complex power of the constant base $N$) is complex-differentiable at $z$, with
--   $$\frac{d}{dz}\left(-\frac{N^{z}}{z}\right) = \frac{N^{z}}{z^{2}} - \frac{(\log N)\, N^{z}}{z},$$
--   where $\log N$ denotes the real natural logarithm of $N$.
--
--   This is a quotient-rule computation for the entire function $z \mapsto N^z = e^{z \log N}$ divided by the coordinate $z$, valid away from the pole at $z = 0$.
--
--   In the PNT+ project this derivative formula handles the boundary term $-N^{1-s}/(1-s)$ of the truncated zeta representation $\zeta_0$ (after the substitution $z = 1-s$), contributing one of the explicit summands of $\zeta_0'$ used in derivative bounds for the Riemann zeta function.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1054-L1068

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

theorem HasDerivAt_cpow_over_var (N : ℕ) {z : ℂ} (z_ne_zero : z ≠ 0) :
    HasDerivAt (fun z ↦ -(N : ℂ) ^ z / z)
      (((N : ℂ) ^ z / z ^ 2) - (Real.log N * N ^ z / z)) z := by sorry
