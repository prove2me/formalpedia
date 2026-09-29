-- Prove2me | Theorems.Thm_fixed_matrix_centered_sampling_markov_tail_from_q_moment_bound_of_nonneg_threshold
-- name    : fixed_matrix_centered_sampling_markov_tail_from_q_moment_bound_of_nonneg_threshold
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T08:47:38.484392+00:00
-- url     : https://prove2.me/theorems/f22de60f-3948-41a1-b8d7-d63e8dd8b56b
-- statement:
--   This is the corrected raw Markov tail step for the fixed-matrix centered sampling fluctuation.  Let
--
--   $$
--   Z(Omega)=left|p^{-1}(P_Omega-pI)Xight|.
--   $$
--
--   Assume the threshold $t$ is nonnegative and that, for an integer $qge1$,
--
--   $$
--   mathbb E[Z^q]le t^q n^{-eta},qquad n=max(n_1,n_2),quad eta>2.
--   $$
--
--   Then the threshold event has probability at least
--
--   $$
--   mathbb P(Zle t)ge 1-n^{-eta}.
--   $$
--
--   The nonnegativity hypothesis on $t$ is essential: the deprecated predecessor allowed $t<0$, in which case the event $Zle t$ can be impossible even when the moment bound is true for the zero matrix.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem fixed_matrix_centered_sampling_markov_tail_from_q_moment_bound_of_nonneg_threshold :
    ∀ (β threshold : ℝ), 2 < β → 0 ≤ threshold →
      ∀ (n₁ n₂ m q : ℕ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ → 1 ≤ q →
        bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              spectralNorm
                (centeredSamplingFluctuation Omega
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          threshold ^ q * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              CenteredSamplingSpectralBound Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X threshold) ≥
          1 - (1 : ℝ) * Real.rpow (↑(max n₁ n₂)) (-β) := by
  sorry
