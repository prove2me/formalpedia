-- Prove2me | Theorems.Thm_HefferonLinAlg_orthogonal_projection_decomposition
-- name    : HefferonLinAlg.orthogonal_projection_decomposition
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-08-05T05:33:52.283398+00:00
-- url     : https://prove2.me/theorems/818abec6-683f-4ff0-96a1-ac233228fcfb
-- title:
--   A subspace and its orthogonal complement split the space
-- statement:
--   Let $S$ be a subspace of a finite-dimensional real inner product space $V$. Then $S$ and its orthogonal complement $S^{\perp}$ are complementary: they intersect only in the zero vector and together span $V$. Equivalently, every vector splits uniquely as its orthogonal projection into $S$ plus a vector orthogonal to $S$ — the payoff of Gram-Schmidt and the result behind the least-squares Topic that closes Hefferon's Chapter Three.
-- source:
--   Jim Hefferon, *Linear Algebra*, Saint Michael's College, 2020 printing, Chapter Three, Section VI.3, Theorem 3.4, p. 298

import Mathlib

open Matrix

namespace HefferonLinAlg

theorem orthogonal_projection_decomposition
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (S : Submodule ℝ V) :
    IsCompl S Sᗮ := by
  sorry

end HefferonLinAlg
