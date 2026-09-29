-- Prove2me | solution 1 for mme_released_global_outer_loss_budget
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:13:19.51552+00:00
-- url     : https://prove2.me/submissions/c72aa878-3143-4bbd-ad08-b09bb36bab0d

import Definitions.Def_mme_released_global_profile_data

open scoped BigOperators
open MME MME.ReleasedGlobal

/-- The proposed complete outer rate bounds admit strictly smaller nonnegative
extraction rates while losing less than one millionth in their total. -/
theorem solution
    (hbase : ∀ owner : Fin 6,
      (((![1490665311, 1490664887, 1490666224, 1490666463, 1490663626, 1490666061] : Fin 6 → ℕ) owner : ℝ) / 1000000000) ≤
        (profile owner).rate (fun _ ↦ 1)) :
    ∃ rho : Fin 6 → ℝ, (∀ owner, 0 ≤ rho owner) ∧
      (∀ owner, rho owner < (profile owner).rate (fun _ ↦ 1)) ∧
      (6707994429 / 125000000 - 1 / 1000000 : ℝ) ≤ 6 * ∑ owner, rho owner := by
  let rho : Fin 6 → ℝ := fun owner ↦
    ((![1490665311, 1490664887, 1490666224, 1490666463, 1490663626, 1490666061] : Fin 6 → ℕ) owner : ℝ) / 1000000000 -
      1 / 1000000000
  refine ⟨rho, ?_, ?_, ?_⟩
  · intro owner
    fin_cases owner <;> norm_num [rho]
  · intro owner
    have h := hbase owner
    dsimp only [rho]
    linarith
  · norm_num [Fin.sum_univ_succ, rho]


#print axioms solution
