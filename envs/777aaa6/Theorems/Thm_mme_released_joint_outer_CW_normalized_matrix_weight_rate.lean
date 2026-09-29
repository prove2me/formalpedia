-- Prove2me | Theorems.Thm_mme_released_joint_outer_CW_normalized_matrix_weight_rate
-- name    : mme_released_joint_outer_CW_normalized_matrix_weight_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T22:31:15.139988+00:00
-- url     : https://prove2.me/theorems/5476004e-e7ce-4e71-8f5e-d3d2f1bebc72
-- title:
--   The joint outer rate transfers to CW powers with exact multiplicity
-- statement:
--   For six admissible outer extraction rates, any matrix extraction from the joint window product transfers to a direct sum of CW-five powers. The number of source copies is exactly the product of the sixth powers of the six input multiplicities. This factor is separated from the exponential matrix-weight lower bound, leaving the sum of the six outer rates and the inner rate. The source input counts retain their polynomial upper bounds. This supplies the normalized extraction used by the final exponent criterion; the numerical rate surplus is a separate requirement.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_joint_outer_inner_matrix_weight_rate
import Theorems.Thm_mme_profiled_CW_permuted_source_product_restrict_power
import Theorems.Thm_mme_six_input_multiplicity_log_rate
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.ReleasedGlobal
  MME.MoreAsymmetryExactSeed MME.GlobalCW
open MME.ReleasedJointInterior (roleEquiv)
universe u

theorem mme_released_joint_outer_CW_normalized_matrix_weight_rate
    {K : Type u} [Field K] (rho : Fin 6 → ℝ)
    (hrho : ∀ owner, 0 ≤ rho owner)
    (hgap : ∀ owner, rho owner < (profile owner).rate (fun _ ↦ 1)) :
    ∃ eps0 : ℝ, 0 < eps0 ∧ ∃ k0 : ℕ,
      ∀ eps : ℝ, 0 < eps → eps ≤ eps0 → ∀ k : ℕ, k0 ≤ k →
      ∀ tau rate : ℝ,
      (∀ (hk : 0 < k ^ 2) (reference : ∀ owner, Reference owner (k ^ 2)),
        ∃ (q : ℕ) (a b c : Fin q → ℕ), 0 < q ∧
          Restrict (bigAdd (fun j => MMObj K (a j) (b j) (c j)))
            (sixSymmetrization (kronFin 6 (fun owner =>
              permObj (roleEquiv owner) (tensor K
                ((frame owner (k ^ 2) hk (reference owner)).window
                  (windowGood owner (k ^ 2) eps)))))) ∧
          Real.exp rate ≤ ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ tau) →
      ∃ (inputs : Fin 6 → ℕ) (q : ℕ) (a b c : Fin q → ℕ),
        (∀ owner, 1 ≤ inputs owner) ∧
        (∀ owner, inputs owner ≤ (blocks (k ^ 2) + 1) ^ 10935) ∧ 0 < q ∧
        Restrict (bigAdd (fun j => MMObj K (a j) (b j) (c j)))
          (bigAdd (fun _ : Fin (∏ owner, inputs owner ^ 6) =>
            (CWObj K 5).kronPow (144 * blocks (k ^ 2)))) ∧
        ((∏ owner, inputs owner ^ 6 : ℕ) : ℝ) *
          Real.exp (6 * (∑ owner, rho owner * (blocks (k ^ 2) : ℝ)) + rate) ≤
          ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ tau := by sorry
