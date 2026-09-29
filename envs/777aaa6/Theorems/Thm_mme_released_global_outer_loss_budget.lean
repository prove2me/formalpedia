-- Prove2me | Theorems.Thm_mme_released_global_outer_loss_budget
-- name    : mme_released_global_outer_loss_budget
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T15:13:15.029502+00:00
-- url     : https://prove2.me/theorems/1b9d94b7-fc59-4798-8a9c-89333f2f9f64
-- title:
--   Complete outer rate bounds admit strict extraction gaps
-- statement:
--   Assuming the six stated complete actual outer rate bounds, explicit nonnegative extraction rates are strictly smaller than the corresponding actual rates, and their sixfold sum loses less than one millionth. The complete rate premises remain separate obligations. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Definitions.Def_mme_released_global_profile_data
open scoped BigOperators
open MME MME.ReleasedGlobal

theorem mme_released_global_outer_loss_budget
    (hbase : ∀ owner : Fin 6,
      (((![1490665311, 1490664887, 1490666224, 1490666463, 1490663626, 1490666061] : Fin 6 → ℕ) owner : ℝ) / 1000000000) ≤
        (profile owner).rate (fun _ ↦ 1)) :
    ∃ rho : Fin 6 → ℝ, (∀ owner, 0 ≤ rho owner) ∧
      (∀ owner, rho owner < (profile owner).rate (fun _ ↦ 1)) ∧
      (6707994429 / 125000000 - 1 / 1000000 : ℝ) ≤ 6 * ∑ owner, rho owner := by sorry
