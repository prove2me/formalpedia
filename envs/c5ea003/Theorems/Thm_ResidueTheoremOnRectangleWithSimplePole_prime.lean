-- Prove2me | Theorems.Thm_ResidueTheoremOnRectangleWithSimplePole_prime
-- name    : ResidueTheoremOnRectangleWithSimplePole_prime
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T16:45:30.969935+00:00
-- url     : https://prove2.me/theorems/de1ab0a9-354d-4b8c-b836-bb3f087bdb7a
-- title:
--   Residue theorem on a rectangle with one simple pole: $\frac{1}{2\pi i}\oint_{\partial R} f = A$
-- statement:
--   Let $z,w\in\mathbb{C}$ with $\operatorname{Re} z\le\operatorname{Re} w$ and $\operatorname{Im} z\le\operatorname{Im} w$, and let $R$ denote the closed rectangle with corners $z$ and $w$. Let $p$ be a point interior to $R$ (the rectangle is a neighborhood of $p$), and let $f\colon\mathbb{C}\to\mathbb{C}$ be holomorphic on $R\setminus\{p\}$. Assume $f$ has a simple pole at $p$ with residue $A$ in the bounded-remainder sense:
--
--   $$f(s) - \frac{A}{s-p} \;=\; O(1)\qquad (s\to p,\ s\ne p).$$
--
--   Then the normalized rectangle contour integral picks out exactly the residue:
--
--   $$\frac{1}{2\pi i}\oint_{\partial R} f(s)\,ds \;=\; A,$$
--
--   where the contour integral is the sum of the four side integrals of the rectangle traversed counterclockwise (the development's `RectangleIntegral'`, which carries the $\frac{1}{2\pi i}$ normalization).
--
--   This is the special case of the residue theorem tailored to the rectangle-based contour calculus of the project: rather than general cycles and winding numbers, everything is done with axis-parallel rectangles, for which holomorphy on the punctured rectangle plus a single simple pole yields the residue directly.
--
--   It is the engine that produces the main term in the Prime Number Theorem: applied to the Perron integrand $-\frac{\zeta'}{\zeta}(s)\,\mathcal{M}(\widetilde{1_\varepsilon})(s)\,X^{s}$ on a rectangle containing $s=1$, it evaluates the difference between the original and the pulled contour as the residue $\mathcal{M}(\widetilde{1_\varepsilon})(1)\,X\approx X$.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/ResidueCalcOnRectangles.lean#L593-L606

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Definitions.Def_Rectangle_defs
import Definitions.Def_ResidueCalcOnRectangles_defs

open Complex BigOperators Nat Classical Real Topology Filter
open Set MeasureTheory intervalIntegral Asymptotics

open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f g : ℂ → E} {z w p c A : ℂ}
  {x x₁ x₂ y y₁ y₂ σ : ℝ}

theorem ResidueTheoremOnRectangleWithSimplePole_prime {f : ℂ → ℂ} {z w p A : ℂ}
    (zRe_le_wRe : z.re ≤ w.re) (zIm_le_wIm : z.im ≤ w.im)
    (pInRectInterior : Rectangle z w ∈ 𝓝 p) (fHolo : HolomorphicOn f (Rectangle z w \ {p}))
    (near_p : (f - (fun s ↦ A / (s - p))) =O[𝓝[≠] p] (1 : ℂ → ℂ)) :
    RectangleIntegral' f z w = A := by sorry
