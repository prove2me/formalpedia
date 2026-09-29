-- Prove2me | Theorems.Thm_schatten_norm_le_rank_rpow_smul_spectral_norm
-- name    : schatten_norm_le_rank_rpow_smul_spectral_norm
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-23T18:38:30.550221+00:00
-- url     : https://prove2.me/theorems/a46a3f72-11df-45d5-a2bd-a8cccb896d95
-- statement:
--   For a real $n_1\times n_2$ matrix $X$ and any exponent $q\ge 1$, the Schatten-$q$ norm is controlled by the rank and the spectral norm: $\lVert X\rVert_{S_q}\le r^{1/q}\,\lVert X\rVert$, where $r=\operatorname{rank}(X)$ (`Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin X))`), $\lVert X\rVert_{S_q}=\bigl(\sum_k\sigma_k(X)^q\bigr)^{1/q}$ is `schattenNorm q X`, and $\lVert X\rVert=\sigma_0(X)$ is `spectralNorm X`. The bound holds because every singular value satisfies $\sigma_k\le\sigma_0=\lVert X\rVert$ and only the first $r$ singular values are nonzero, so $\sum_k\sigma_k^q\le r\,\sigma_0^q$ and hence $\bigl(\sum_k\sigma_k^q\bigr)^{1/q}\le r^{1/q}\,\sigma_0$. With $q\ge\log r$ the prefactor $r^{1/q}$ collapses to $\le e^{1/2}$ (the window-collapse handled separately by Node-B / `gram_schatten_le_exp_half_variance_scale`). Source: Candès–Recht 2009 (arXiv:0805.4471), §6.1, the operator/Schatten comparison right after Lemma 6.1; Horn–Johnson §5.6, §7.3.
-- source:
--   Candès–Recht, 'Exact Matrix Completion via Convex Optimization', arXiv:0805.4471, §6.1 (operator/Schatten comparison after Lemma 6.1); Horn–Johnson, Matrix Analysis, §5.6/§7.3.

import Definitions.Def_matrix_completion_schatten
import Mathlib.Analysis.InnerProductSpace.SingularValues
open MatrixCompletion

theorem schatten_norm_le_rank_rpow_smul_spectral_norm :
    ∀ {n1 n2 : ℕ} (q : ℝ) (X : Matrix (Fin n1) (Fin n2) ℝ),
      1 ≤ q →
        schattenNorm q X ≤
          Real.rpow
            ((Module.finrank ℝ (LinearMap.range (Matrix.toEuclideanLin X)) : ℝ)) q⁻¹
            * spectralNorm X := by sorry
