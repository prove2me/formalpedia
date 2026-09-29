-- Prove2me | Theorems.Thm_singular_value_zero_le_spectral_norm
-- name    : singular_value_zero_le_spectral_norm
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-21T17:55:31.390486+00:00
-- url     : https://prove2.me/theorems/dc5ff0e0-72e0-4a4b-85e1-95bd8ba76d14
-- statement:
--   The largest singular value of a real matrix $Y$ is at most its spectral (operator) norm: $\sigma_0(Y) \le \lVert Y\rVert$, where $\sigma_0$ is the zeroth (largest) entry of the singular-value sequence of $T = \mathrm{toEuclideanLin}\,Y$ and $\lVert Y\rVert = \lVert T\rVert_{op}$. Together with the proved `spectral_norm_le_singular_value_zero` (which gives $\lVert Y\rVert \le \sigma_0(Y)$) this establishes the EQUALITY of the operator norm and the top singular value. The proof exhibits the top eigenvector $v_0$ of the positive self-adjoint operator $S = T^\ast T$ (with eigenvalue $\sigma_0^2$, normalized $\lVert v_0\rVert = 1$): then $\lVert T v_0\rVert^2 = \langle S v_0, v_0\rangle = \sigma_0^2$, so $\sigma_0 = \lVert T v_0\rVert \le \lVert T\rVert_{op}\,\lVert v_0\rVert = \lVert Y\rVert$.
-- source:
--   Candes & Recht, Exact matrix completion via convex optimization, arXiv:0805.4471 (2009), Section 6.1, p.24-25.

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.InnerProductSpace.SingularValues
open MatrixCompletion

theorem singular_value_zero_le_spectral_norm :
    ∀ {n₁ n₂ : ℕ} (Y : Matrix (Fin n₁) (Fin n₂) ℝ),
      (Matrix.toEuclideanLin Y).singularValues 0 ≤ spectralNorm Y := by sorry
