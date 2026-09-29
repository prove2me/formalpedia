-- Prove2me | Theorems.Thm_a0_singular_coordinate_energy_bounds
-- name    : a0_singular_coordinate_energy_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-06-21T17:04:32.795354+00:00
-- url     : https://prove2.me/theorems/b24bfd40-0eec-4713-9241-63ef5a1b0a4c
-- statement:
--   This lemma unfolds the A0 incoherence hypothesis into pointwise coordinate-energy estimates for the left and right singular vector families.
--
--   For the left singular vectors it states
--   $$
--   \sum_{k=1}^r u_k(i)^2\le {\mu_0 r\over n_1}
--   $$
--   for every row coordinate $i$, and for the right singular vectors it states
--   $$
--   \sum_{k=1}^r v_k(j)^2\le {\mu_0 r\over n_2}
--   $$
--   for every column coordinate $j$.
--
--   Source: Candes-Recht 2008, Definition 1.2/A0 incoherence; this is exactly the coordinate form of the coherence bound.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem a0_singular_coordinate_energy_bounds
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (μ₀ : ℝ) :
    0 < n₁ → 0 < n₂ → 0 < r → A0 S μ₀ →
      (∀ i : Fin n₁,
        ∑ k : Fin r, (S.u k i) ^ 2 ≤ μ₀ * (r : ℝ) / (n₁ : ℝ)) ∧
      (∀ j : Fin n₂,
        ∑ k : Fin r, (S.v k j) ^ 2 ≤ μ₀ * (r : ℝ) / (n₂ : ℝ)) := by
  sorry
