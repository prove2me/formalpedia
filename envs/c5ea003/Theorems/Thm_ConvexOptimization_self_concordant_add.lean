-- Prove2me | Theorems.Thm_ConvexOptimization_self_concordant_add
-- name    : ConvexOptimization.self_concordant_add
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T16:12:34.176291+00:00
-- url     : https://prove2.me/theorems/2ce4a1eb-e3ec-4142-a1ac-71b911dec445
-- title:
--   Sums of self-concordant functions
-- statement:
--   **Self-concordance is preserved by addition.**
--
--   Let $\Omega \subseteq \mathbb{R}^n$ be open and let $f$ and $h$ both be self-concordant on $\Omega$ — convex, $C^3$, and satisfying $|\varphi'''(0)| \le 2\varphi''(0)^{3/2}$ for every line restriction $\varphi(t) = f(x + tv)$ with $x \in \Omega$. Then $f + h$ is self-concordant on $\Omega$:
--
--   $$f, h \text{ self-concordant on } \Omega \;\Longrightarrow\; f + h \text{ self-concordant on } \Omega .$$
--
--   The proof is the elementary inequality $|u + v| \le 2(a^{3/2} + b^{3/2}) \le 2(a+b)^{3/2}$ for the pieces, and the practical consequence is a *calculus*: a barrier assembled from many self-concordant terms is self-concordant, so one never verifies the third-derivative condition for a composite function directly.
--
--   **Formalization Note** Openness of `Ω` is an explicit hypothesis, and it is genuinely needed: at a boundary point the iterated derivatives of the line restriction are junk values and the inequality would be asserted about meaningless quantities. Source: B&V §9.6.1, p. 497.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 499, §9.6.1 (self-concordance is preserved by addition). Openness of the domain is an explicit hypothesis: the line-restriction derivatives carry junk values at boundary points

import Mathlib
import Definitions.Def_ConvexOptimization_selfConcordance

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.self_concordant_add {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩo : IsOpen Ω) (f h : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : IsSelfConcordantOn Ω f) (hh : IsSelfConcordantOn Ω h) :
    IsSelfConcordantOn Ω (f + h) := by
  sorry
