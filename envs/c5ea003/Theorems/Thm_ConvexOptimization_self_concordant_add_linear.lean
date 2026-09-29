-- Prove2me | Theorems.Thm_ConvexOptimization_self_concordant_add_linear
-- name    : ConvexOptimization.self_concordant_add_linear
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-13T16:13:02.397931+00:00
-- url     : https://prove2.me/theorems/38a68f4b-3ab2-4c74-b903-8be62755eab6
-- title:
--   Self-concordance is stable under affine additions
-- statement:
--   **Self-concordance is preserved by adding an affine function.**
--
--   Let $\Omega \subseteq \mathbb{R}^n$ be open, let $f$ be self-concordant on $\Omega$, and let $c \in \mathbb{R}^n$, $r \in \mathbb{R}$. Then
--
--   $$x \;\longmapsto\; f(x) + \langle c, x\rangle + r$$
--
--   is self-concordant on $\Omega$.
--
--   An affine term contributes nothing to the second or third derivative of any line restriction, so both sides of the defining inequality are unchanged. Together with closure under sums this is what makes the barrier objective tractable: adding the scaled objective $t f_0$ to the barrier $\varphi$ preserves self-concordance whenever $f_0$ is affine — the case of linear programming — and more generally reduces the verification to $f_0$ alone.
--
--   **Formalization Note** Openness of `Ω` is required for the same reason as in the additivity statement: the line-restriction derivatives are only meaningful at interior points. Source: B&V §9.6.1, p. 497.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 499, §9.6.1 (self-concordance is preserved by scaling and by adding an affine function)

import Mathlib
import Definitions.Def_ConvexOptimization_selfConcordance

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.self_concordant_add_linear {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (hΩo : IsOpen Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsSelfConcordantOn Ω f)
    (c : EuclideanSpace ℝ (Fin n)) (r : ℝ) :
    IsSelfConcordantOn Ω (fun x => f x + ⟪c, x⟫ + r) := by
  sorry
