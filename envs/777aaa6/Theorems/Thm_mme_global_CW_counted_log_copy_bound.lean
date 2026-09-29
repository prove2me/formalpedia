-- Prove2me | Theorems.Thm_mme_global_CW_counted_log_copy_bound
-- name    : mme_global_CW_counted_log_copy_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T07:59:08.125025+00:00
-- url     : https://prove2.me/theorems/2eba734a-dc7d-4069-876b-163517ef7d71
-- title:
--   Certified logarithmic copies from the global counting scale
-- statement:
--   For a realized exact global stage, the explicit logarithmic bound log(target count) minus the AP-free loss, log(64 times the counting scale), and the repair exponent times log 8 guarantees the ceiling of the requested exponential number of copies. Integer rounding and repair batches are included.
-- source:
--   Finite global stage of More Asymmetry Proposition 5.1 / Theorem 5.3.

import Definitions.Def_mme_global_CW_counted_stage
import Definitions.Def_mme_global_CW_counting_data
open BigOperators MME MME.TensorObj MME.ProfiledCW MME.RecursiveYZ MME.GlobalCW MME.RecursiveXHash MME.HashExtraction
open scoped Classical
set_option autoImplicit false
universe u

theorem mme_global_CW_counted_log_copy_bound {ell M : ℕ} (D : CountedStage ell M) (E : ExactStage ell M)
    (hlower : D.lower ≤ E.hash.lower) (hexponent : E.repairExponent = D.repairExponent)
    (a : ℝ) (ha : 0 ≤ a) (hbudget : a ≤ D.certifiedLogCopies) :
    ⌈Real.exp a⌉₊ ≤ E.copies := by
  sorry
