-- Prove2me | Definitions.Def_fenchelConjugate
-- name    : fenchelConjugate
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-11T21:36:56.057931+00:00
-- url     : https://prove2.me/theorems/27f62e21-0acb-4c2d-8b8e-8e8a1bed24e7
-- title:
--   Fenchel conjugate $f^*$
-- statement:
--   The **Fenchel conjugate** (or convex conjugate, or Legendre–Fenchel transform) of a function.
--
--   For $f : \mathbb{R}^n \to \mathbb{R}$ and $y \in \mathbb{R}^n$,
--
--   $$f^{*}(y) \;=\; \sup_{x \in \mathbb{R}^n}\bigl(\langle x, y\rangle - f(x)\bigr) \;\in\; (-\infty, +\infty] .$$
--
--   Geometrically, $f^{*}(y)$ is the largest gap between the linear function $x \mapsto \langle x,y\rangle$ and $f$; equivalently, $-f^{*}(y)$ is the intercept of the highest affine function of slope $y$ lying below $f$. The conjugate is convex and closed no matter what $f$ is, being a pointwise supremum of affine functions of $y$.
--
--   Conjugation is the central duality operation of convex analysis: it exchanges a function with the family of affine minorants describing it, converts sums into infimal convolutions, and turns the Lagrange dual of an optimization problem into an explicit formula in terms of $f_0^{*}$. Fenchel's inequality $\langle x,y\rangle \le f(x) + f^{*}(y)$ is immediate from the definition.
--
--   **Formalization Note** The value is `EReal`-valued and defined as a supremum in that complete lattice, so it always exists and is the true least upper bound rather than a junk value; it equals $+\infty$ exactly when the difference is unbounded above. The function $f$ is finite-valued (`ℝ`-valued), which is the setting of the book's §3.3. Source: B&V §3.3.1, pp. 90–91.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 90-91, §3.3.1 eq. (3.18) (definition of the conjugate function)

import Mathlib

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace ConvexOptimization

/-- **Fenchel conjugate** `f*(y) = sup_x (⟪x,y⟫ − f x)` of a finite-valued
function, valued in `EReal` (B&V §3.3). -/
noncomputable def fenchelConjugate {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (y : EuclideanSpace ℝ (Fin n)) : EReal :=
  ⨆ x : EuclideanSpace ℝ (Fin n), ((⟪x, y⟫ - f x : ℝ) : EReal)

end ConvexOptimization


