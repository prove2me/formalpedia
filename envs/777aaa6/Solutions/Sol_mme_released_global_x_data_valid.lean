-- Prove2me | solution 1 for mme_released_global_x_data_valid
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T11:57:14.695991+00:00
-- url     : https://prove2.me/submissions/3d55b3e5-34f1-4583-a14b-78b2fca5c9f1

import Definitions.Def_mme_released_global_x_certificate
open BigOperators MME MME.ReleasedGlobal MME.ReleasedGlobalNumeric
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000

theorem solution :
    (∀ o s, 0 ≤ alphaQ o s) ∧
    (∀ o, ∑ s, alphaQ o s = 1) ∧
    (∀ o i, ∑ j, marginalQ o i j = 1) ∧
    (∀ o i j, 0 < dualCounts o i j) ∧
    (∀ o, 0 < dualTotal o) ∧
    (∀ o, ∑ s, dualQ o s = 1) ∧
    (∀ o s, 0 < dualQ o s) ∧
    (∀ o j, 0 ≤ marginalQ o 0 j) ∧
    (∀ o s, xInputs o ⟨s.val,by omega⟩ = alphaQ o s) ∧
    (∀ o s, xInputs o ⟨45+s.val,by omega⟩ = dualQ o s) ∧
    (∀ o j, xInputs o ⟨90+j.val,by omega⟩ = marginalQ o 0 j) ∧
    (∀ o, rateFloor o ≤ xBound o) := by
  decide +kernel
