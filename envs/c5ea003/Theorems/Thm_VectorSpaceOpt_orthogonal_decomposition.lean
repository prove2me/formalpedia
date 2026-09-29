-- Prove2me | Theorems.Thm_VectorSpaceOpt_orthogonal_decomposition
-- name    : VectorSpaceOpt.orthogonal_decomposition
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T21:23:18.41607+00:00
-- url     : https://prove2.me/theorems/921ac3fb-4b2a-4740-b290-80d71195743c
-- title:
--   Orthogonal decomposition: H = M ⊕ M⊥ and M = M⊥⊥
-- statement:
--   Let $M$ be a **closed** subspace of a real Hilbert space $H$, and write $M^\perp$ for its **orthogonal complement**, the set of vectors orthogonal to every element of $M$. The theorem makes two claims.
--
--   **1. Direct sum decomposition.** Every $x \in H$ has a **unique** representation as a sum of a vector in $M$ and a vector in $M^\perp$:
--
--   $$H = M \oplus M^\perp, \qquad x = m + n \ \text{ with } \ m \in M,\ n \in M^\perp.$$
--
--   **2. The double complement returns the subspace.**
--
--   $$M^{\perp\perp} = M.$$
--
--   Both follow from the projection theorem: $m$ is the orthogonal projection of $x$ onto $M$ and $n = x - m$ is the error, which is orthogonal to $M$. Uniqueness comes from the Pythagorean theorem. Closedness of $M$ is essential to both claims — for a dense proper subspace, $M^\perp = \{0\}$ and $M^{\perp\perp}$ is all of $H$.
--
--   **Formalization Note.** The unique decomposition is stated as unique existence of the ordered pair $(m, n)$, not merely of each component separately.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §3.4, Theorem 1, p. 53

import Mathlib
open scoped RealInnerProductSpace

namespace VectorSpaceOpt

theorem orthogonal_decomposition {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (M : Submodule ℝ H) (hM : IsClosed (M : Set H)) :
    (∀ x : H, ∃! p : H × H, p.1 ∈ M ∧ p.2 ∈ Mᗮ ∧ x = p.1 + p.2) ∧ Mᗮᗮ = M := by sorry

end VectorSpaceOpt
