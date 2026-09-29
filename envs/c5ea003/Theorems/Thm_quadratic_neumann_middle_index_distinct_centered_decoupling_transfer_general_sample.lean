-- Prove2me | Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_decoupling_transfer_general_sample
-- name    : quadratic_neumann_middle_index_distinct_centered_decoupling_transfer_general_sample
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-01T11:05:54.843173+00:00
-- url     : https://prove2.me/theorems/ea270d99-c620-47d2-aa51-d1428191f189
-- statement:
--   General-sample (constant/`Φ`-scale) two-variable decoupling transfer for the
--   centered `ω₁ = ω₃ ≠ ω₂` quadratic contribution (middle index).
--
--   This is the §6.3 summary-scale analogue of
--   `quadratic_neumann_middle_index_distinct_centered_decoupling_transfer`: a
--   high-probability two-copy (pair) Bernoulli estimate for the decoupled
--   contribution at an arbitrary nonnegative `scale` implies the corresponding
--   one-copy estimate, with only universal constant loss.  Unlike the `lam`-form
--   node, the threshold `scale` is a free parameter (so it can be instantiated at
--   the four-term Section 6.3 summary scale `Φ`), and there is no weak `μ₀^{4/3}`
--   sample lower bound baked in.
-- source:
--   Candes, Emmanuel, and Benjamin Recht. "Exact matrix completion via convex optimization." Communications of the ACM 55.6 (2012): 111-119.

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion

theorem quadratic_neumann_middle_index_distinct_centered_decoupling_transfer_general_sample :
    ∃ Cdecouple cdecouple : ℝ, 0 < Cdecouple ∧ 0 < cdecouple ∧
      ∀ {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
        (S : SVD M r) (p Cdec cdec β scale : ℝ),
        0 ≤ p → p ≤ 1 → 0 < Cdec → 0 < cdec → 0 ≤ scale →
        bernoulliPairEventProb p
            (fun Omega1 Omega2 =>
              spectralNorm
                (quadraticNeumannMiddleIndexDistinctCenteredDecoupledContribution
                  Omega1 Omega2 S p) ≤
                Cdec * scale) ≥
          1 - cdec * Real.rpow (↑(max n₁ n₂)) (-β) →
        bernoulliEventProb p
            (fun Omega =>
              spectralNorm
                (quadraticNeumannMiddleIndexDistinctCenteredContribution Omega S p) ≤
                (Cdecouple * Cdec) * scale) ≥
          1 - (cdecouple * cdec) * Real.rpow (↑(max n₁ n₂)) (-β) := by sorry
