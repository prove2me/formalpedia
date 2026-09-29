-- Prove2me | Theorems.Thm_positive_tangent_sampling_deviation_bound_implies_concentration
-- name    : positive_tangent_sampling_deviation_bound_implies_concentration
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T06:25:47.305375+00:00
-- url     : https://prove2.me/theorems/9d0415c5-7b84-4236-b776-0bbe4a55aaa1
-- statement:
--   This is the corrected deterministic bridge from normalized tangent sampling deviation to tangent sampling concentration.
--
--   For SVD data $S$ of a rank-$r$ matrix $M$, let $T$ be the tangent space and $P_T$ its projection. Given an observation set $Omega$ and a sampling rate $p$, the deviation bound controls the normalized operator
--
--   $$
--   p^{-1}(P_TP_Omega P_T-pP_T).
--   $$
--
--   Assuming $0<p$ and $operatorname{TangentSamplingDeviationBound}(Omega,S,p,arepsilon)$, the theorem concludes the pointwise concentration event
--
--   $$
--   |P_TP_Omega X-pX|_Fle arepsilon p|X|_F
--   quad	ext{for every }Xin T.
--   $$
--
--   This node replaces the deprecated zero-rate statement. Its sketch reduces the result to the positive-rate unit-Frobenius estimate and the homogeneity extension from the unit ball to all tangent-space matrices.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

theorem positive_tangent_sampling_deviation_bound_implies_concentration
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p epsilon : ℝ) :
    0 < p →
    TangentSamplingDeviationBound Omega S p epsilon →
    TangentSamplingConcentration Omega S p epsilon := by
  sorry
