-- Prove2me | Theorems.Thm_VectorSpaceOpt_projection_orthogonality
-- name    : VectorSpaceOpt.projection_orthogonality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-23T21:22:48.554899+00:00
-- url     : https://prove2.me/theorems/6fbdcc74-3aa2-4696-96a2-4201e21003e0
-- title:
--   Projection theorem in pre-Hilbert space: orthogonality characterizes the best approximation
-- statement:
--   Let $X$ be a real **pre-Hilbert space** — an inner product space, not assumed complete — and let $M$ be a subspace of $X$. Fix a vector $x \in X$ and a vector $m_0 \in M$. Two claims are made about $m_0$.
--
--   **1. Orthogonality characterizes minimality.** The vector $m_0$ is a best approximation to $x$ from $M$ if and only if the error vector $x - m_0$ is **orthogonal** to $M$:
--
--   $$\big(\ \|x - m_0\| \le \|x - m\| \ \text{ for all } m \in M\ \big) \iff \big(\ \langle x - m_0,\, m\rangle = 0 \ \text{ for all } m \in M\ \big).$$
--
--   **2. A minimizing vector is unique.** If $m_1 \in M$ and $m_0$ both minimize $\|x - m\|$ over $M$, then $m_1 = m_0$.
--
--   Existence of a minimizing vector is deliberately **not** asserted here. Existence requires completeness of the space and closedness of the subspace, and is the content of the classical projection theorem; the two claims above hold in any inner product space.
--
--   **Formalization Note.** The subspace carries no closedness hypothesis, and the ambient space no completeness hypothesis — the statement is exactly as general as the source's pre-Hilbert version.
-- source:
--   David G. Luenberger, Optimization by Vector Space Methods, John Wiley & Sons, 1969, §3.3, Theorem 1, p. 50

import Mathlib
open scoped RealInnerProductSpace

namespace VectorSpaceOpt

theorem projection_orthogonality {X : Type} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (M : Submodule ℝ X) (x : X) (m₀ : X) (hm₀ : m₀ ∈ M) :
    ((∀ m ∈ M, ‖x - m₀‖ ≤ ‖x - m‖) ↔ (∀ m ∈ M, ⟪x - m₀, m⟫ = 0)) ∧
    (∀ m₁ ∈ M, (∀ m ∈ M, ‖x - m₁‖ ≤ ‖x - m‖) → (∀ m ∈ M, ‖x - m₀‖ ≤ ‖x - m‖) →
      m₁ = m₀) := by sorry

end VectorSpaceOpt
