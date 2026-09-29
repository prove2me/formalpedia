-- Prove2me | Theorems.Thm_tangent_sampling_deviation_eq_tangent_bilinear_supremum_of_nonnegative_rate
-- name    : tangent_sampling_deviation_eq_tangent_bilinear_supremum_of_nonnegative_rate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-25T06:19:36.376444+00:00
-- url     : https://prove2.me/theorems/3abf870f-0e7f-4d2c-9e9b-9870e6e171b2
-- statement:
--   This theorem is the corrected Frobenius-duality step in the Appendix 9.1 representation of the tangent sampling deviation.
--
--   For a sample set $\Omega$, sampling rate $p$, and tangent projection $P_T$, the project variable is
--   $$
--   Z(\Omega)=\sup_{X\in T,\ \|X\|_F\le1}
--   p^{-1}\|P_TP_\Omega X-pX\|_F.
--   $$
--   When $p\ge0$, Frobenius duality rewrites this as
--   $$
--   \sup_{\|X_1\|_F\le1,\ X_2\in T,\ \|X_2\|_F\le1}
--   p^{-1}\langle X_1,P_TP_\Omega X_2-pX_2\rangle_F.
--   $$
--   The nonnegativity condition is essential because the scalar $p^{-1}$ sits outside the norm.  The earlier no-rate variant was too strong; the paper only applies this with $p=m/(n_1n_2)\ge0$.
--
--   Source location: Candes-Recht 2008, Appendix 9.1, PDF p. 46, the display after equation (9.2), plus standard finite-dimensional Frobenius duality.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_talagrand_tangent_bilinear
open MatrixCompletion

theorem tangent_sampling_deviation_eq_tangent_bilinear_supremum_of_nonnegative_rate
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    0 ≤ p →
    tangentSamplingDeviation Omega S p =
      tangentSamplingTangentBilinearDeviation Omega S p := by
  sorry
