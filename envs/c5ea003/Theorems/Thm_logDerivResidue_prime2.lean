-- Prove2me | Theorems.Thm_logDerivResidue_prime2
-- name    : logDerivResidue_prime2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:42:35.483601+00:00
-- url     : https://prove2.me/theorems/e4bd0a6d-16c0-40d4-bda1-8c7dd12df3d8
-- title:
--   Local boundedness of $\frac{f'}{f} + \frac{1}{s-p}$ on a punctured neighborhood of a simple pole
-- statement:
--   Let $f : \mathbb{C} \to \mathbb{C}$, let $p \in \mathbb{C}$, and let $U$ be a neighborhood of $p$. Assume $f$ is holomorphic and nonvanishing on $U \setminus \{p\}$, and that for some constant $A \neq 0$ the difference $f(s) - \dfrac{A}{s-p}$ is bounded on $U \setminus \{p\}$. Then there exists a neighborhood $V$ of $p$ such that
--
--   $$s \;\longmapsto\; \left\| \frac{f'(s)}{f(s)} + \frac{1}{s - p} \right\| \quad \text{is bounded above on } V \setminus \{p\}.$$
--
--   This restates the $O(1)$ behavior of the corrected logarithmic derivative near a simple pole in explicitly quantified form: rather than an asymptotic estimate along the punctured neighborhood filter, it produces a concrete neighborhood $V$ on which a uniform bound holds.
--
--   The bounded-on-a-neighborhood formulation is the shape consumed by the removable-singularity and rectangle-integral lemmas: it certifies that $f'/f + (s-p)^{-1}$ extends holomorphically across $p$, so that in the zeta application $-\zeta'/\zeta(s) - \frac{1}{s-1}$ is holomorphic near $s = 1$ and contour integrals through that region are well controlled.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L415-L422

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

theorem logDerivResidue_prime2 {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (non_zero : ∀ x ∈ U \ {p}, f x ≠ 0)
    (holc : HolomorphicOn f (U \ {p}))
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, BddAbove (norm ∘ (deriv f * f⁻¹ + (fun s ↦ (s - p)⁻¹)) '' (V \ {p})) := by sorry
