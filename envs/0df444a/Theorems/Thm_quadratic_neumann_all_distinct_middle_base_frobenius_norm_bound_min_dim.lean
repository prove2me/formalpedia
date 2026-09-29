-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_middle_base_frobenius_norm_bound_min_dim
-- name    : quadratic_neumann_all_distinct_middle_base_frobenius_norm_bound_min_dim
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-01T09:51:14.416906+00:00
-- url     : https://prove2.me/theorems/50b301fc-b3e6-4cb5-81a3-ed166e525803
-- statement:
--   Rectangular `min(n₁,n₂)`-denominator Frobenius/variance-proxy bound for the
--   conditional middle base matrix in the all-distinct quadratic Neumann term.
--
--   This is the sound `min`-denominator analogue of the Disproved max-form node
--   `quadratic_neumann_all_distinct_middle_base_frobenius_norm_bound`.  On the inner
--   coefficient event each entry is a controlled `G_{ω₂}` coefficient times one
--   tangent-coordinate kernel; the row/column-summed kernel-square estimate from A0
--   is governed by `min(n₁,n₂)` (CR §6.3, the kernel scale after eq (6.2)--(6.4)).
--
--   Source: Candès--Recht 2008, PDF p. 31, Lemma 6.8 equation (6.22), with the
--   rectangular `min(n₁,n₂)` kernel convention stated after equations (6.2)--(6.4).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_distinct_middle_base_frobenius_norm_bound_min_dim :
    ∃ Cfro : ℝ, 0 < Cfro ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ (Omega3 : Finset (Fin n₁ × Fin n₂)) (p innerBound : ℝ),
        0 ≤ innerBound →
        QuadraticAllDistinctInnerCoefficientBound Omega3 S p innerBound →
        ∀ w1 : Fin n₁ × Fin n₂,
          frobeniusNorm
              (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) ≤
            Cfro * innerBound *
              Real.sqrt (μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) := by sorry
