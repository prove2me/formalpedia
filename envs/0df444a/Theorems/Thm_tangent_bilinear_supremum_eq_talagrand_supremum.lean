-- Prove2me | Theorems.Thm_tangent_bilinear_supremum_eq_talagrand_supremum
-- name    : tangent_bilinear_supremum_eq_talagrand_supremum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T06:20:02.889895+00:00
-- url     : https://prove2.me/theorems/d4131a0e-fbbf-4825-8e9e-447d7fe66f07
-- statement:
--   This theorem is the coordinate-expansion step in the Appendix 9.1 representation of the tangent sampling deviation.
--
--   Starting from the tangent-restricted bilinear expression
--   $$
--   \sup_{\|X_1\|_F\le1,\ X_2\in T,\ \|X_2\|_F\le1}
--   p^{-1}\langle X_1,P_TP_\Omega X_2-pX_2\rangle_F,
--   $$
--   expand $P_\Omega$ in the coordinate basis.  With
--   $$
--   y_{ij}=P_T(e_i e_j^\top),\qquad \delta_{ij}=1_{(i,j)\in\Omega},
--   $$
--   the expression becomes the Appendix 9.1 supremum
--   $$
--   \sup_{\|X_1\|_F,\|X_2\|_F\le1}
--   \sum_{i,j}(\delta_{ij}-p)p^{-1}
--   \langle X_1,y_{ij}\rangle_F\langle y_{ij},X_2\rangle_F.
--   $$
--   The theorem also records the standard projection observation that the restriction $X_2\in T$ can be removed because the coefficients depend only on $P_TX_2$.
--
--   Source location: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation (9.2), where $Z$ is written as the displayed coordinate supremum over $X_1$ and $X_2$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand_tangent_bilinear
open MatrixCompletion

theorem tangent_bilinear_supremum_eq_talagrand_supremum
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    tangentSamplingTangentBilinearDeviation Omega S p =
      tangentSamplingTalagrandSupremumDeviation Omega S p := by
  sorry
