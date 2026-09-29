-- Prove2me | Theorems.Thm_bernoulli_tangent_sampling_concentration_from_positive_deviation_bound
-- name    : bernoulli_tangent_sampling_concentration_from_positive_deviation_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T06:26:05.178164+00:00
-- url     : https://prove2.me/theorems/6bacf1ac-8721-41bb-8810-a9ae7fbfce98
-- statement:
--   This theorem lifts the corrected positive-rate deterministic implication to the Bernoulli sampling model.
--
--   Let $Omega$ be drawn by including each matrix entry independently with probability $p$. If $0<ple1$ and the deviation event
--
--   $$
--   operatorname{TangentSamplingDeviationBound}(Omega,S,p,arepsilon)
--   $$
--
--   has probability at least
--
--   $$
--   1-c,n^{-eta},qquad n=max(n_1,n_2),
--   $$
--
--   then the tangent concentration event
--
--   $$
--   |P_TP_Omega X-pX|_Fle arepsilon p|X|_F
--   quad (Xin T)
--   $$
--
--   has the same probability lower bound. The proof is a monotonicity argument: for positive $p$, the deterministic corrected theorem maps every deviation-good observation set to a concentration-good observation set, and Bernoulli event probability is monotone under implication.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

theorem bernoulli_tangent_sampling_concentration_from_positive_deviation_bound
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p epsilon c β : ℝ) :
    0 < p → p ≤ 1 →
    bernoulliEventProb p
        (fun Omega => TangentSamplingDeviationBound Omega S p epsilon) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) →
    bernoulliEventProb p
        (fun Omega => TangentSamplingConcentration Omega S p epsilon) ≥
        1 - c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
