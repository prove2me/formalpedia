-- Prove2me | Theorems.Thm_mme_released_joint_interior_zero_owner_output
-- name    : mme_released_joint_interior_zero_owner_output
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T10:32:10.972974+00:00
-- url     : https://prove2.me/theorems/b71ff942-4809-4351-9bc0-72d723e576bf
-- title:
--   Zero-weight owners contribute a scalar matrix
-- statement:
--   A zero-weight owner has no physical positions. Its exact graded and useful output admits all words and contributes a scalar matrix after six symmetrization, for any owner mode order. The root exponent bound remains a separate obligation.
-- source:
--   Checked tensor restrictions and released global histogram extraction.

import Definitions.Def_mme_released_joint_interior_frame
import Theorems.Thm_mme_profiled_CW_empty_six_extraction
open MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
open MME.ReleasedJointInterior MME.MoreAsymmetryExactSeed
universe u

theorem mme_released_joint_interior_zero_owner_output
    {K : Type u} [Field K] (k : ℕ) (j : Fin 270) (hw : weight j = 0)
    (a : ∀ r : Fin 6, Address 4 270 (parent r) (size r k))
    {L N : ℕ} (e : Fin L ≃ Position (fun r => size r k j))
    (length : L * 2 ^ (2 - 1) = N) (sigma : Equiv.Perm (Fin 3)) :
    Restrict (MMObj K 1 1 1)
      (sixSymmetrization (ProfiledCW.tensor K (fun i x =>
        Graded (ReleasedInterior.parent_total (component j).2) (sigma.symm i)
          (fun r t => (splitEquiv r j).symm (a r j t))
          (ProfiledCW.split e length x) ∧
        Useful (fullCell (ReleasedInterior.parent_total (component j).2)
          (fun r t => (splitEquiv r j).symm (a r j t)))
          (fun c w => k * weight j * ReleasedInterior.integerProfile
            (component j).1 (component j).2 (sigma.symm i) c w)
          (ProfiledCW.split e length x)))) := by sorry
