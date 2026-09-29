-- Prove2me | Theorems.Thm_mme_released_joint_outer_inner_matrix_weight_rate
-- name    : mme_released_joint_outer_inner_matrix_weight_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T16:18:49.958983+00:00
-- url     : https://prove2.me/theorems/5369fe7a-2d2e-45fe-b959-5154d18609ab
-- title:
--   Six actual outer extractions retain the joint window rate
-- statement:
--   The six actual outer hashing steps compose with a matrix family in the joint outer window product. Their outer copy rates and polynomial source multiplicities remain explicit under the common tolerance and scale threshold. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Theorems.Thm_mme_released_global_simultaneous_uniform_window_extraction
import Theorems.Thm_mme_permuted_product_extraction_six_matrix_weight_rate
import Definitions.Def_mme_released_joint_interior_profiles
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.ReleasedGlobal
  MME.MoreAsymmetryExactSeed MME.GlobalCW
open MME.ReleasedJointInterior (roleEquiv)
universe u

theorem mme_released_joint_outer_inner_matrix_weight_rate
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
          (sixSymmetrization (kronFin 6 (fun owner => permObj (roleEquiv owner)
            (bigAdd (fun _ : Fin (inputs owner) =>
              tensor K (fun _ (_ : FineWord (4 * blocks (k ^ 2))) => True)))))) ∧
        Real.exp (6 * (∑ owner,
          (rho owner * (blocks (k ^ 2) : ℝ) + Real.log (inputs owner : ℝ))) + rate) ≤
          ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ tau := by sorry
