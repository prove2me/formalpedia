-- Prove2me | Theorems.Thm_VectorSpaceOpt_mazur_geometric_hahn_banach_nonempty
-- name    : VectorSpaceOpt.mazur_geometric_hahn_banach_nonempty
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-06T00:55:20.186716+00:00
-- url     : https://prove2.me/theorems/b2fc0ef8-e358-4aa5-a84f-5f20b7511376
-- title:
--   §5.12, Theorem 1 — Mazur geometric Hahn–Banach theorem
-- statement:
--   Let $X$ be a real normed space, $K \subseteq X$ a convex set with nonempty interior, and $V \subseteq X$ a **nonempty** linear variety (affine subspace) containing no point of $\operatorname{int} K$. Then there exist a nonzero continuous linear functional $f \colon X \to \mathbb R$ and a scalar $c$ such that
--
--   $$
--   f(v)=c\quad(\forall v\in V),\qquad f(k)<c\quad(\forall k\in\operatorname{int}K).
--   $$
--
--   Thus a single closed affine hyperplane contains all of $V$ while the interior of $K$ lies strictly on one side of it. This is the chapter's geometric Hahn–Banach form and is the common separation engine behind the supporting-hyperplane and two-set separation milestones.
--
--   **Why this statement carries an extra hypothesis.** The existing platform node [`VectorSpaceOpt.mazur_geometric_hahn_banach`](p2m:theorem/ef624c10-1e53-4228-8828-8a803c601f3f) omits the nonemptiness of $V$ and is therefore refutable in Lean, for a formalization reason rather than a mathematical one: Mathlib's `AffineSubspace ℝ X` is allowed to be empty, and `⊥ : AffineSubspace ℝ X` has no points. For $K = \operatorname{univ}$ and $V = \bot$ the hypothesis "$V$ meets no interior point of $K$" is vacuous, yet the conclusion would demand a nonzero continuous functional bounded strictly above on all of $X$, which is impossible. Luenberger's §5.12 tacitly assumes a genuine linear variety $V = x_0 + M$, which is never empty. That defect was diagnosed and disproved on the platform by Shuze Chen, who proposed exactly this repair. This node is that repair, published so the mission milestone has a provable target; Mazur's theorem itself is unchanged.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, §5.12, Theorem 1, book p. 133 (PDF physical p. 153), https://sites.science.oregonstate.edu/~show/old/142_Luenberger.pdf. Repaired formalization of VectorSpaceOpt.mazur_geometric_hahn_banach (nonemptiness hypothesis on the linear variety V added).

import Mathlib

namespace VectorSpaceOpt

/-- Luenberger, §5.12, Theorem 1, with the nonemptiness of the linear variety `V`
made explicit. -/
theorem mazur_geometric_hahn_banach_nonempty
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K : Set X) (hK : Convex ℝ K) (hKint : (interior K).Nonempty)
    (V : AffineSubspace ℝ X) (hV0 : (V : Set X).Nonempty)
    (hV : ∀ v ∈ V, v ∉ interior K) :
    ∃ (f : X →L[ℝ] ℝ) (c : ℝ),
      f ≠ 0 ∧ (∀ v ∈ V, f v = c) ∧ (∀ k ∈ interior K, f k < c) := by
  sorry

end VectorSpaceOpt
