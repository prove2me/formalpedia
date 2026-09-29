-- Prove2me | Theorems.Thm_tangent_diagonal_multiplier_spectral_norm_le_universal_multiple
-- name    : tangent_diagonal_multiplier_spectral_norm_le_universal_multiple
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-22T00:28:24.335574+00:00
-- url     : https://prove2.me/theorems/710529b1-eb19-47d7-8f7c-60c04ab3abb8
-- statement:
--   This is the universal version of the diagonal multiplier estimate from Lemma 6.4.
--
--   For a fixed matrix $X$, Lemma 6.4 considers
--   $$
--   Z=\sum_{a,b} X_{ab}\,\langle P_T(e_ae_b^*),e_ae_b^*\rangle e_ae_b^*.
--   $$
--   The paper rewrites this as
--   $$
--   Z=\Lambda_U X(I-\Lambda_V)+X\Lambda_V,
--   $$
--   where $\Lambda_U$ and $\Lambda_V$ are diagonal matrices with entries $\|P_Ue_a\|^2$ and $\|P_Ve_b\|^2$. Since those diagonal entries lie in $[0,1]$, this gives
--   $$
--   \|Z\|\le C_D\|X\|
--   $$
--   with a universal constant, for instance $C_D=2$.
--
--   Source: Candes-Recht 2008, PDF p. 27, Lemma 6.4, especially equations (6.10)--(6.11).
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem tangent_diagonal_multiplier_spectral_norm_le_universal_multiple :
    ∃ Cdiag : ℝ, 0 < Cdiag ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → A0 S μ₀ →
        spectralNorm (tangentDiagonalMultiplier S X) ≤
          Cdiag * spectralNorm X := by
  sorry
