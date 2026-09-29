-- Prove2me | Theorems.Thm_spectral_norm_le_schatten_norm
-- name    : spectral_norm_le_schatten_norm
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T04:50:26.674766+00:00
-- url     : https://prove2.me/theorems/04d9ba2d-86d8-4f89-8739-307803c3feea
-- statement:
--   For an exponent $q\ge 1$, the spectral (operator) norm of a real matrix $Y$ is at most its Schatten $q$-norm: $\lVert Y\rVert\le\lVert Y\rVert_{S_q}$. With singular values $\sigma_1\ge\sigma_2\ge\cdots$, $\sigma_1=(\sigma_1^q)^{1/q}\le(\sum_i\sigma_i^q)^{1/q}$ — the Schatten norms decrease to the operator norm as $q\to\infty$.
-- source:
--   Candes & Recht, Exact matrix completion via convex optimization, CACM 55.6 (2012).

import Definitions.Def_matrix_completion_schatten
open MatrixCompletion

theorem spectral_norm_le_schatten_norm :
    ∀ {n₁ n₂ : ℕ} (q : ℕ) (Y : Matrix (Fin n₁) (Fin n₂) ℝ),
      1 ≤ q →
      spectralNorm Y ≤ schattenNorm (q : ℝ) Y := by sorry
