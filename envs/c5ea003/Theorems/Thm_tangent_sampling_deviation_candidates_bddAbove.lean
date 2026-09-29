-- Prove2me | Theorems.Thm_tangent_sampling_deviation_candidates_bddAbove
-- name    : tangent_sampling_deviation_candidates_bddAbove
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T06:42:10.545918+00:00
-- url     : https://prove2.me/theorems/8062f752-b955-4231-8bed-f940305c012c
-- statement:
--   This leaf supplies the boundedness hypothesis needed to use the supremum in the definition of tangent sampling deviation.
--
--   For fixed SVD data $S$, observation set $Omega$, and rate $p$, consider the finite-dimensional candidate set
--
--   $$
--   left{p^{-1}|P_TP_Omega X-pX|_F:
--   Xin T, |X|_Fle1ight}subsetmathbb R.
--   $$
--
--   The theorem asserts that this set is bounded above. Mathematically this follows because $P_T$, $P_Omega$, and the identity map are linear operators on a finite-dimensional real matrix space, and a linear operator is bounded on the Frobenius unit ball. This is separated as its own leaf so the parent concentration argument can use the supremum cleanly.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

theorem tangent_sampling_deviation_candidates_bddAbove
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    BddAbove {v : ℝ |
      ∃ X : Matrix (Fin n₁) (Fin n₂) ℝ,
        tangentProjection S X = X ∧ frobeniusNorm X ≤ 1 ∧
          v = (p⁻¹) *
            frobeniusNorm
              (tangentProjection S (samplingProjection Omega X) - p • X)} := by
  sorry
