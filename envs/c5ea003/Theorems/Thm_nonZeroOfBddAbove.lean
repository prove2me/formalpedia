-- Prove2me | Theorems.Thm_nonZeroOfBddAbove
-- name    : nonZeroOfBddAbove
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:44:31.042362+00:00
-- url     : https://prove2.me/theorems/6f7eebab-d69e-401b-9313-e324bd78e372
-- title:
--   A function with a nonzero simple-pole principal part is nonvanishing near the pole
-- statement:
--   Let $f : \mathbb{C} \to \mathbb{C}$, let $p \in \mathbb{C}$, and let $U$ be a neighborhood of $p$. Suppose $A \in \mathbb{C}$ is a nonzero constant such that the difference between $f$ and the model simple pole $s \mapsto A(s-p)^{-1}$ has bounded norm on the punctured set $U \setminus \{p\}$; that is, the set
--
--   $$\left\{\, \left| f(s) - \frac{A}{s-p} \right| \;:\; s \in U \setminus \{p\} \,\right\}$$
--
--   is bounded above. Then there exists an open neighborhood $V$ of $p$ such that
--
--   $$f(s) \neq 0 \quad \text{for all } s \in V \setminus \{p\}.$$
--
--   Intuitively, if $f$ behaves like $A/(s-p)$ with $A \neq 0$ up to a bounded error, then $|f(s)| \to \infty$ as $s \to p$, so $f$ cannot vanish in a small enough punctured neighborhood of $p$. In the PNT+ project this abstract lemma is applied to $\zeta$ (and to $-\zeta'/\zeta$) at $s = 1$: knowing that $\zeta(s) - (s-1)^{-1}$ stays bounded near $1$ yields the nonvanishing of $\zeta$ in a punctured neighborhood of $s = 1$, a fact needed for the zero-free region and residue computations.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ZetaBounds.lean#L210-L264

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

theorem nonZeroOfBddAbove {f : ℂ → ℂ} {p : ℂ} {U : Set ℂ}
    (U_in_nhds : U ∈ 𝓝 p) {A : ℂ} (A_ne_zero : A ≠ 0)
    (f_near_p : BddAbove (norm ∘ (f - fun s ↦ A * (s - p)⁻¹) '' (U \ {p}))) :
    ∃ V ∈ 𝓝 p, IsOpen V ∧ ∀ s ∈ V \ {p}, f s ≠ 0 := by sorry
