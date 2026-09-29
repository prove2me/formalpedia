-- Prove2me | Theorems.Thm_Zeta23_Analytic_residueTheorem_finset
-- name    : Zeta23.Analytic.residueTheorem_finset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:39:54.877348+00:00
-- url     : https://prove2.me/theorems/f1e14088-fb5d-44bb-ad85-682ad865a085
-- title:
--   Residue theorem on a rectangle for finitely many simple poles
-- statement:
--   Let $z, w \in \mathbb{C}$ with $\operatorname{Re} z \le \operatorname{Re} w$ and $\operatorname{Im} z \le \operatorname{Im} w$, spanning the closed rectangle $R$. Let $S$ be a finite set of points, each interior to $R$ (i.e. $R$ is a neighbourhood of each $p \in S$), and let $A : \mathbb{C} \to \mathbb{C}$ assign a prospective residue to each point. Suppose $f : \mathbb{C} \to \mathbb{C}$ is holomorphic (complex differentiable) on $R \setminus S$, and that at each $p \in S$ the difference
--   $$f(s) - \frac{A(p)}{s - p} \;=\; O(1) \quad \text{as } s \to p$$
--   (along the punctured neighbourhood filter) — that is, $f$ has at worst a simple pole at $p$ with residue $A(p)$.
--
--   **Statement.** The normalized rectangle contour integral (`RectangleIntegral'`, the integral over the boundary $\partial R$ divided by $2\pi i$) satisfies
--   $$\frac{1}{2\pi i}\oint_{\partial R} f(s)\, ds \;=\; \sum_{p \in S} A(p).$$
--
--   This is the residue theorem on a rectangle for finitely many simple poles. In the module `Zeta23.Analytic.RectangleLogDeriv` it is the base case for the project's contour calculus: it is consumed by the weighted argument principle `Zeta23.Analytic.rectangleIntegralPrime_mul_logDeriv_of_poles`, which in turn drives both the Riemann–von Mangoldt zero count and the Weil explicit-formula contour identity.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Analytic/RectangleLogDeriv.lean#L30-L139

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Definitions.Def_Extra_Zeta23_Analytic_RectangleLogDeriv
import Definitions.Def_Zeta23_Analytic_RectangleLogDeriv
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles

open Complex Set Topology Filter Asymptotics Real
open Zeta23
open Analytic

theorem Zeta23.Analytic.residueTheorem_finset {f : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re) (him : z.im ≤ w.im)
    (S : Finset ℂ) (A : ℂ → ℂ)
    (hS : ∀ p ∈ S, Rectangle z w ∈ 𝓝 p)
    (fHolo : HolomorphicOn f (Rectangle z w \ (S : Set ℂ)))
    (near : ∀ p ∈ S, (f - fun s => A p / (s - p)) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f z w = ∑ p ∈ S, A p := by sorry
