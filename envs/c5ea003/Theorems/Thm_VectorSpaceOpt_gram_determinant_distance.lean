-- Prove2me | Theorems.Thm_VectorSpaceOpt_gram_determinant_distance
-- name    : VectorSpaceOpt.gram_determinant_distance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T21:24:06.803896+00:00
-- url     : https://prove2.me/theorems/b8dc9965-b2fe-4cff-90d5-802248c36aea
-- title:
--   Gram determinant formula for the minimum distance
-- statement:
--   Let $y_1, \dots, y_n$ be **linearly independent** vectors in a real inner product space $H$, let $M$ be the subspace they generate, and let $x \in H$. Write
--
--   $$\delta = \min_{m \in M}\, \|x - m\|$$
--
--   for the minimum distance from $x$ to $M$ (attained, since $M$ is finite-dimensional and hence complete). Then $\delta$ is given by a ratio of **Gram determinants**:
--
--   $$\delta^2 = \frac{g(y_1, \dots, y_n,\, x)}{g(y_1, \dots, y_n)},$$
--
--   where $g$ denotes the determinant of the matrix of pairwise inner products, and the numerator is formed from the family $y_1, \dots, y_n$ **extended by $x$** in the last position.
--
--   The formula follows by adjoining the equation $\delta^2 = \langle x - \hat x,\, x\rangle$ to the normal equations and applying Cramer's rule to the resulting system of $n+1$ linear equations. It is of theoretical rather than computational interest: evaluating an $(n+1)$-dimensional determinant is about as costly as inverting an $n$-dimensional matrix.
--
--   **Formalization Note.** The minimum is written as an infimum over the span; the extended family places $x$ after $y_1, \dots, y_n$, which fixes the numerator's Gram matrix up to the symmetric reordering that leaves its determinant unchanged.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §3.6, Theorem 1, p. 57

import Mathlib
open scoped RealInnerProductSpace

namespace VectorSpaceOpt

theorem gram_determinant_distance {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (y : Fin n → H) (hy : LinearIndependent ℝ y)
    (x : H) :
    (⨅ m : Submodule.span ℝ (Set.range y), ‖x - (m : H)‖) ^ 2 =
      (Matrix.of fun i j : Fin (n + 1) => ⟪(Fin.snoc y x : Fin (n + 1) → H) i, (Fin.snoc y x : Fin (n + 1) → H) j⟫).det /
      (Matrix.of fun i j : Fin n => ⟪y i, y j⟫).det := by sorry

end VectorSpaceOpt
