-- Prove2me | Theorems.Thm_quadratic_neumann_all_distinct_middle_base_entry_sup_norm_bound_min_dim
-- name    : quadratic_neumann_all_distinct_middle_base_entry_sup_norm_bound_min_dim
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-01T09:49:53.774899+00:00
-- url     : https://prove2.me/theorems/a23addce-e3d3-41e4-9925-aa0b1f8a40be
-- statement:
--   Rectangular `min(n₁,n₂)`-denominator entry sup-norm bound for the conditional
--   middle base matrix in the all-distinct quadratic Neumann term.
--
--   Sound `min`-denominator analogue of the Disproved max-form node
--   `quadratic_neumann_all_distinct_middle_base_entry_sup_norm_bound`.  On the inner
--   coefficient event each entry is a controlled `G_{ω₂}` coefficient (`≤ innerBound`)
--   times one tangent-coordinate kernel `⟪P_T(eᵢeⱼᵀ), e_{w₁}⟫ ≤ Cker·μ₀·(r/min)` (A0).
--
--   Source: Candès--Recht 2008, PDF p. 31, Lemma 6.8 equation (6.22), with the
--   rectangular `min(n₁,n₂)` kernel convention stated after equations (6.2)--(6.4).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_all_distinct_middle_base_entry_sup_norm_bound_min_dim :
    ∃ Centry : ℝ, 0 < Centry ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ (Omega3 : Finset (Fin n₁ × Fin n₂)) (p innerBound : ℝ),
        0 ≤ innerBound →
        QuadraticAllDistinctInnerCoefficientBound Omega3 S p innerBound →
        ∀ w1 : Fin n₁ × Fin n₂,
          entrySupNorm
              (quadraticAllDistinctMiddleBaseMatrix Omega3 S p w1) ≤
            Centry * innerBound * μ₀ *
              ((r : ℝ) / (↑(min n₁ n₂))) := by sorry
