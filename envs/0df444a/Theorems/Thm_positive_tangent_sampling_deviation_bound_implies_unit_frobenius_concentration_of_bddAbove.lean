-- Prove2me | Theorems.Thm_positive_tangent_sampling_deviation_bound_implies_unit_frobenius_concentration_of_bddAbove
-- name    : positive_tangent_sampling_deviation_bound_implies_unit_frobenius_concentration_of_bddAbove
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T06:41:51.960238+00:00
-- url     : https://prove2.me/theorems/927e9f4b-8872-47bb-a91e-239c321a9f5d
-- statement:
--   This is the order-theoretic core of the positive-rate tangent deviation argument.
--
--   Fix SVD data $S$ for a matrix $M$, an observation set $Omega$, and a positive sampling rate $p>0$. The normalized tangent deviation is the supremum of the candidate set
--
--   $$
--   left{p^{-1}|P_TP_Omega X-pX|_F:
--   Xin T, |X|_Fle1ight}.
--   $$
--
--   Assuming this candidate set is bounded above, the theorem says that a deviation bound $Zlearepsilon$ implies the unit-ball estimate
--
--   $$
--   |P_TP_Omega X-pX|_Fle arepsilon p
--   quad	ext{for every }Xin T	ext{ with }|X|_Fle1.
--   $$
--
--   The proof is purely formal: a candidate value is at most the supremum, the supremum is at most $arepsilon$, and multiplying by the positive number $p$ cancels $p^{-1}$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

theorem positive_tangent_sampling_deviation_bound_implies_unit_frobenius_concentration_of_bddAbove
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p epsilon : ℝ) :
    BddAbove {v : ℝ |
      ∃ X : Matrix (Fin n₁) (Fin n₂) ℝ,
        tangentProjection S X = X ∧ frobeniusNorm X ≤ 1 ∧
          v = (p⁻¹) *
            frobeniusNorm
              (tangentProjection S (samplingProjection Omega X) - p • X)} →
    0 < p →
    TangentSamplingDeviationBound Omega S p epsilon →
    ∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
      tangentProjection S X = X →
      frobeniusNorm X ≤ 1 →
      frobeniusNorm
          (tangentProjection S (samplingProjection Omega X) - p • X) ≤
        epsilon * p := by
  sorry
