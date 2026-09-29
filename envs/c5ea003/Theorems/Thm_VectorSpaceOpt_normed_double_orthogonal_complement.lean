-- Prove2me | Theorems.Thm_VectorSpaceOpt_normed_double_orthogonal_complement
-- name    : VectorSpaceOpt.normed_double_orthogonal_complement
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T15:51:34.18433+00:00
-- url     : https://prove2.me/theorems/d43e9551-9555-4bbd-9f1c-d8060011f7d3
-- title:
--   The annihilator identity ⊥(M⊥) = M for closed subspaces
-- statement:
--   In a normed space, orthogonality is defined through the dual rather than through an inner product: $x \in X$ and $x^* \in X^*$ are **orthogonal** when $\langle x, x^*\rangle = 0$. For a subset $S \subseteq X$, the complement $S^\perp \subseteq X^*$ consists of the functionals annihilating $S$; for a subset $U \subseteq X^*$, the complement ${}^\perp U \subseteq X$ consists of the vectors annihilated by every member of $U$.
--
--   Let $M$ be a **closed** subspace of a real normed space $X$. Then
--
--   $${}^\perp\big(M^\perp\big) = M,$$
--
--   that is, a vector is annihilated by every bounded functional vanishing on $M$ exactly when it belongs to $M$.
--
--   The inclusion $M \subseteq {}^\perp(M^\perp)$ is immediate. For the converse, take $x \notin M$ and define $f(\alpha x + m) = \alpha$ on $[x + M]$; because $M$ is closed, $\inf_m \|x + m\| > 0$ and $f$ is bounded, so Hahn–Banach extends it to some $x^* \in X^*$. That $x^*$ vanishes on $M$ but has $\langle x, x^*\rangle = 1$, so $x \notin {}^\perp(M^\perp)$.
--
--   Closedness is essential: for a dense proper subspace, $M^\perp = \{0\}$ and the left-hand side is all of $X$.
--
--   **Formalization Note.** Stated pointwise as an equivalence for each $x$, with both annihilator conditions written out as explicit quantifications over continuous linear functionals rather than through a named annihilator construction.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §5.7, Theorem 1, p. 118

import Mathlib

namespace VectorSpaceOpt

theorem normed_double_orthogonal_complement {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (M : Submodule ℝ X) (hM : IsClosed (M : Set X)) (x : X) :
    (∀ f : X →L[ℝ] ℝ, (∀ m ∈ M, f m = 0) → f x = 0) ↔ x ∈ M := by sorry

end VectorSpaceOpt
