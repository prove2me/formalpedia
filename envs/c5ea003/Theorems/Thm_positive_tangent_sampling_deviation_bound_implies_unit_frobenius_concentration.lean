-- Prove2me | Theorems.Thm_positive_tangent_sampling_deviation_bound_implies_unit_frobenius_concentration
-- name    : positive_tangent_sampling_deviation_bound_implies_unit_frobenius_concentration
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T06:25:29.7836+00:00
-- url     : https://prove2.me/theorems/7b2e92ca-2959-4128-bad9-cae79f5aa6f5
-- statement:
--   This is the corrected positive-rate version of the unit-ball step in the tangent sampling concentration argument.
--
--   Let $Min mathbb R^{n_1	imes n_2}$ be represented by SVD data $S$, and let $T$ be its tangent space with projection $P_T$. For an observation set $Omega$, write $P_Omega$ for the coordinate sampling projection. The normalized tangent sampling deviation is
--
--   $$
--   Z(Omega,S,p)=sup_{Xin T, |X|_Fle 1}
--   p^{-1}|P_TP_Omega X-pX|_F.
--   $$
--
--   The theorem says that if the Bernoulli sampling rate is genuinely positive, $0<p$, and $Z(Omega,S,p)le arepsilon$, then every tangent-space matrix $X$ in the Frobenius unit ball satisfies
--
--   $$
--   |P_TP_Omega X-pX|_Fle arepsilon p.
--   $$
--
--   The positivity hypothesis is essential: the deprecated non-positive version is false at $p=0$, because Lean's total inverse has $0^{-1}=0$.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_tangent

open MatrixCompletion

theorem positive_tangent_sampling_deviation_bound_implies_unit_frobenius_concentration
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p epsilon : ℝ) :
    0 < p →
    TangentSamplingDeviationBound Omega S p epsilon →
    ∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
      tangentProjection S X = X →
      frobeniusNorm X ≤ 1 →
      frobeniusNorm
          (tangentProjection S (samplingProjection Omega X) - p • X) ≤
        epsilon * p := by
  sorry
