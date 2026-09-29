-- Prove2me | Theorems.Thm_mme_CW_square_2376_profile_hash_pruned_cores
-- name    : mme_CW_square_2376_profile_hash_pruned_cores
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T15:55:57.011198+00:00
-- url     : https://prove2.me/theorems/9221d28c-368f-4f56-b98f-c578b480e1d0
-- title:
--   Rate-form five-grade hash-pruned profile cores
-- statement:
--   For every field, there is a nonnegative loss rate $r_m\to0$ such that, for all sufficiently large exact-profile scales $m$, a direct sum of $s_m$ copies of the finite profile core restricts from $T_6^{\otimes 6{,}000{,}000m}$ and $$\left(H e^{-r_m}\right)^{3{,}000{,}000m}\le s_m.$$ Here $H$ is the reciprocal marginal-entropy denominator from equation (13). Each core retains the elementary square factor and exactly $616627m$ cyclic-coupled copies. This is the exponential-rate form of type selection and collision pruning.
-- source:
--   Coppersmith--Winograd (1990), equations (11)--(13), Salem--Spencer hashing, collision pruning, and the auxiliary equation on journal pp. 265--269.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_mme_CW_2376_profile_data
import Definitions.Def_mme_CW_tensor
open MME Filter
universe u

theorem mme_CW_square_2376_profile_hash_pruned_cores
    {K : Type u} [Field K] :
    ∃ rate : ℕ → ℝ,
      Tendsto rate atTop (nhds 0) ∧
      (∀ m, 0 ≤ rate m) ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ s : ℕ,
          TensorObj.Restrict
            (TensorObj.bigAdd
              (fun _ : Fin s => cw2376ProfileCore K m))
            ((CWObj K 6).kronPow (6000000 * m)) ∧
          (cw2376ProfileCountBase * Real.exp (-(rate m))) ^
              (3000000 * m) ≤ (s : ℝ) := by
  sorry
