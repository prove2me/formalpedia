-- Prove2me | Theorems.Thm_DerivUpperBnd_aux7_4
-- name    : DerivUpperBnd_aux7_4
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:19:12.331664+00:00
-- url     : https://prove2.me/theorems/84f4a832-4092-4dfe-88bb-fc67303f8fff
-- title:
--   Integrability of $x^{-\sigma-1}\log x$ on $(a,\infty)$
-- statement:
--   Let $a, \sigma \in \mathbb{R}$ with $\sigma > 0$ and $a \geq 1$. Then the function
--   $$x \mapsto x^{-\sigma-1} \log x$$
--   is Lebesgue integrable on the interval $(a, \infty)$ (with respect to Lebesgue measure).
--
--   Since $\sigma > 0$, the exponent $-\sigma - 1$ is strictly less than $-1$, so the power decay dominates the logarithmic growth and the integral converges; the hypothesis $a \geq 1$ keeps the integrand away from the singular behavior of $\log$ at $0$.
--
--   This integrability fact is one of the technical prerequisites for applying the fundamental theorem of calculus and comparison estimates to the tail integrals that arise when bounding $|\zeta'(s)|$ in the zeta-bounds part of the PNT+ project. It is a reusable convergence lemma for power-times-log integrands.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L1636-L1641

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

theorem DerivUpperBnd_aux7_4 {a σ : ℝ} (σpos : 0 < σ) (ha : 1 ≤ a) :
    IntegrableOn (fun x ↦ x ^ (-σ - 1) * Real.log x) (Ioi a) volume := by sorry
