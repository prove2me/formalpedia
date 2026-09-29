-- Prove2me | solution 1 for mme_released_joint_outer_CW_normalized_matrix_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T22:31:17.413686+00:00
-- url     : https://prove2.me/submissions/f03540fd-1703-4fcb-a0fe-a5ae6080beea

import Theorems.Thm_mme_released_joint_outer_inner_matrix_weight_rate
import Theorems.Thm_mme_profiled_CW_permuted_source_product_restrict_power
import Theorems.Thm_mme_six_input_multiplicity_log_rate

open BigOperators MME MME.TensorObj MME.ProfiledCW MME.ReleasedGlobal
  MME.MoreAsymmetryExactSeed MME.GlobalCW
open MME.ReleasedJointInterior (roleEquiv)
universe u

/-- The complete joint window rate transfers to CW powers, with the exact
source multiplicity factored out of its exponential matrix weight. -/
theorem solution
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
          ∑ j, ((a j * b j * c j : ℕ) : ℝ) ^ tau := by
  classical
  obtain ⟨eps0, heps0, k0, houter⟩ :=
    mme_released_joint_outer_inner_matrix_weight_rate (K := K) rho hrho hgap
  refine ⟨eps0, heps0, k0, ?_⟩
  intro eps heps hepsbound k hk tau rate hinner
  obtain ⟨inputs, q, a, b, c, hinputs, hpoly, hq, hr, hw⟩ :=
    houter eps heps hepsbound k hk tau rate hinner
  refine ⟨inputs, q, a, b, c, hinputs, hpoly, hq,
    hr.trans (mme_profiled_CW_permuted_source_product_restrict_power
      (blocks (k ^ 2)) inputs (fun _ _ _ => True) roleEquiv), ?_⟩
  have heq :
      Real.exp (6 * (∑ owner,
        (rho owner * (blocks (k ^ 2) : ℝ) + Real.log (inputs owner : ℝ))) + rate) =
      ((∏ owner, inputs owner ^ 6 : ℕ) : ℝ) *
        Real.exp (6 * (∑ owner, rho owner * (blocks (k ^ 2) : ℝ)) + rate) := by
    rw [show 6 * (∑ owner,
        (rho owner * (blocks (k ^ 2) : ℝ) + Real.log (inputs owner : ℝ))) =
        ∑ owner, (6 * (rho owner * (blocks (k ^ 2) : ℝ)) +
          6 * Real.log (inputs owner : ℝ)) by
      simp only [Finset.mul_sum, mul_add]]
    rw [Real.exp_add, mme_six_input_multiplicity_log_rate inputs hinputs,
      ← Finset.mul_sum, Real.exp_add, mul_assoc]
  rw [heq] at hw
  exact hw


#print axioms solution
