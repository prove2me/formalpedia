-- Prove2me | Theorems.Thm_BookSixth_standard_family_isometry_preserves_roundness
-- name    : BookSixth.standard_family_isometry_preserves_roundness
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T07:52:12.000839+00:00
-- url     : https://prove2.me/theorems/920732b6-4ea4-4c7f-9688-9944f593275b
-- title:
--   One Euclidean similarity moves the whole family of standard circles to a family of round circles
-- statement:
--   Let $A$ be a real $3\times 3$ matrix that preserves the Euclidean inner product $\sum_i x_i y_i$, let $a>0$ and let $b$ be a vector. Then for every index $i$ the image of the standard circle $\texttt{standardCircle i}$ under $x \mapsto a\,A x + b$ is a genuine round circle. The hypothesis is stated for the inner product rather than for a norm because the type $\texttt{Fin 3} \to \mathbb{R}$ in these definitions carries the supremum norm, and a $120^\circ$ rotation about an axis preserves Euclidean lengths but not the supremum norm. The requirement $a>0$ is unavoidable: for $a=0$ the image is the single point $b$, and $\texttt{RoundCircle}$ demands a radius $r>0$.
-- source:
--   This is a three-line adapter over two `Proved` theorems. `BookSixth.standard_circle_is_round` (210c40b4) gives `RoundCircle (standardCircle i)`, and `BookSixth.euclidean_isometry_preserves_roundness` (837c17d9) gives the transport `RoundCircle ((fun x => a • (A x) + b) '' C)` for a `\to L[\mathbb{R}]` map `A` preserving the inner product. The only work is bridging the matrix `A` to its `\to L[\mathbb{R}]` lift: `Matrix.mulVecLin A` is the linear map of `A`, and `LinearMap.toContinuousLinearMap` lifts it (available because `Fin 3 → ℝ` is finite-dimensional, and the target is Hausdorff). Both bridges are `rfl`, so the two functions are definitionally identical.
--
--   **Why the mission needs it.** The open leaf `BookSixth.perfect_circles_pairwise_unlinked_motion` (f6a7245e) asks for an ambient isotopy `K` with the labelled endpoint `(K 1) '' C i = standardCircle i.val` and `RoundCircle ((K t) '' C i)` for all `t, i`. Any family-wide construction reaches the standard configuration and then continues to move it; the conjugate of a similarity is a similarity, so every such continuation must keep every standard circle round. That is precisely this statement, for the target configuration of the leaf.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open scoped Matrix
open BookSixth

theorem BookSixth.standard_family_isometry_preserves_roundness (A : Matrix (Fin 3) (Fin 3) ℝ)
    (hA : ∀ x y : Fin 3 → ℝ, (∑ i, (A *ᵥ x) i * (A *ᵥ y) i) = ∑ i, x i * y i)
    (a : ℝ) (ha : 0 < a) (b : Fin 3 → ℝ) (t : ℝ) (i j : ℕ) (hij : i ≠ j) :
    RoundCircle ((fun x : Space3 => (a • (A *ᵥ x)) + b) '' (standardCircle i)) := by sorry
