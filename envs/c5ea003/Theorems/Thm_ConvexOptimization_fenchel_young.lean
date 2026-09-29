-- Prove2me | Theorems.Thm_ConvexOptimization_fenchel_young
-- name    : ConvexOptimization.fenchel_young
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-11T21:40:55.808538+00:00
-- url     : https://prove2.me/theorems/a6d85ddd-41aa-49fa-9334-e626deb8ddff
-- title:
--   Fenchel–Young inequality
-- statement:
--   **Fenchel's inequality** (also called the Fenchel–Young inequality).
--
--   For $f : \mathbb{R}^n \to \mathbb{R}$ let $f^{*}(y) = \sup_x(\langle x,y\rangle - f(x))$ be its Fenchel conjugate, with values in $(-\infty,+\infty]$. Then for all $x, y \in \mathbb{R}^n$,
--
--   $$\langle x, y\rangle \;\le\; f(x) + f^{*}(y).$$
--
--   The inequality holds for *every* function $f$ — no convexity, continuity or measurability is needed — since it is nothing but the definition of the supremum applied at the point $x$. Equality holds exactly when $y$ is a subgradient of $f$ at $x$, which is how the inequality is used to characterize the solutions of dual pairs of problems.
--
--   Specialized to $f(x) = |x|^{p}/p$ on $\mathbb{R}$, whose conjugate is $|y|^{q}/q$ with $1/p + 1/q = 1$, it becomes Young's inequality $xy \le x^{p}/p + y^{q}/q$, and hence — after integration — Hölder's inequality.
--
--   **Formalization Note** The inequality is stated in `EReal`, adding the real value $f(x)$ (coerced) to the `EReal`-valued conjugate, so the case $f^{*}(y) = +\infty$ needs no separate treatment. Source: B&V §3.3.1, p. 94.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 94, §3.3.2 (Fenchel's inequality; stated unnumbered in the text)

import Mathlib
import Definitions.Def_fenchelConjugate

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.fenchel_young {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ((⟪x, y⟫ : ℝ) : EReal) ≤ (f x : EReal) + fenchelConjugate f y := by
  sorry
