-- Prove2me | Theorems.Thm_Zeta23_Analytic_rectangleIntegralPrime_mul_logDeriv_of_poles
-- name    : Zeta23.Analytic.rectangleIntegralPrime_mul_logDeriv_of_poles
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-17T20:40:20.404957+00:00
-- url     : https://prove2.me/theorems/334363d6-fb9d-4bae-8223-a70eb5d30122
-- title:
--   Weighted argument principle on a rectangle, with poles: $\frac{1}{2\pi i}\oint g\, \frac{f'}{f} = \sum_\rho m_\rho g(\rho) - \sum_p m_p g(p)$
-- statement:
--   Let $z, w \in \mathbb{C}$ with $\operatorname{Re} z \le \operatorname{Re} w$ and $\operatorname{Im} z \le \operatorname{Im} w$, and let $R = [\operatorname{Re} z, \operatorname{Re} w] \times [\operatorname{Im} z, \operatorname{Im} w]$ be the closed rectangle they span. Let $Z, P$ be disjoint finite sets of complex numbers with every $p \in P$ interior to $R$, and let $f, g : \mathbb{C} \to \mathbb{C}$ satisfy:
--
--   - $f$ is analytic on a neighbourhood of every point of $R \setminus P$, and $g$ is analytic on a neighbourhood of every point of $R$;
--   - $f$ does not vanish on the boundary of the rectangle;
--   - on $R \setminus P$, the zeros of $f$ are exactly the elements of $Z$, and $Z \subseteq R$;
--   - at each $p \in P$, $f$ has a pole-type singularity of order $m(p)$: for some $c_p \ne 0$, $(s - p)^{m(p)} f(s) \to c_p$ as $s \to p$ (along the punctured neighbourhood filter).
--
--   **Statement.** Writing $\frac{1}{2\pi i}\oint_{\partial R}$ for the normalized rectangle contour integral (`RectangleIntegral'`),
--   $$\frac{1}{2\pi i}\oint_{\partial R} g(s)\, \frac{f'(s)}{f(s)}\, ds \;=\; \sum_{\rho \in Z} \operatorname{ord}_\rho(f)\, g(\rho) \;-\; \sum_{p \in P} m(p)\, g(p),$$
--   where $\operatorname{ord}_\rho(f)$ is the order of vanishing of $f$ at $\rho$ (`analyticOrderNatAt`).
--
--   This weighted argument principle with poles is the central contour-integration tool of the project, in the module `Zeta23.Analytic.RectangleLogDeriv`. It is consumed by `Zeta23.RvM.rectangleIntegralPrime_logDeriv_completedZeta_eq_Ncount` — the contour-integral evaluation behind the Riemann–von Mangoldt formula for $N(T)$, applied to the completed zeta function with its poles at $0$ and $1$ — and by `Zeta23.WeilEF.rectangle_identity`, the contour identity underlying the Weil-type explicit formula.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/Analytic/RectangleLogDeriv.lean#L164-L347

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

theorem Zeta23.Analytic.rectangleIntegralPrime_mul_logDeriv_of_poles {f g : ℂ → ℂ} {z w : ℂ} (hre : z.re ≤ w.re)
    (him : z.im ≤ w.im) (Z P : Finset ℂ) (hZP : Disjoint Z P)
    (hPint : ∀ p ∈ P, Rectangle z w ∈ 𝓝 p)
    (hf : AnalyticOnNhd ℂ f (Rectangle z w \ (P : Set ℂ)))
    (hg : AnalyticOnNhd ℂ g (Rectangle z w))
    (hborder : ∀ s ∈ RectangleBorder z w, f s ≠ 0)
    (hZ : ∀ s ∈ Rectangle z w \ (P : Set ℂ), f s = 0 ↔ s ∈ Z) (hZsub : (Z : Set ℂ) ⊆ Rectangle z w)
    (m : ℂ → ℕ)
    (hpole : ∀ p ∈ P, ∃ c : ℂ, c ≠ 0 ∧ Tendsto (fun s => (s - p) ^ m p * f s) (𝓝[≠] p) (𝓝 c)) :
    RectangleIntegral' (fun s => g s * logDeriv f s) z w
      = ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) * g ρ - ∑ p ∈ P, (m p : ℂ) * g p := by sorry
