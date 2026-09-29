-- Prove2me | solution 1 for mme_dwz_same_marginal_entropy_values_bddAbove
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T04:04:10.407994+00:00
-- url     : https://prove2.me/submissions/e11cd420-57bd-4798-9215-cea51edd68ff

import Theorems.Thm_mme_dwz_table2_entropy_potential
import Theorems.Thm_mme_modern_entropyBits_additive_certificate

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 300000

namespace MME.DWZSameMarginalBdd

theorem proof :
    BddAbove MME.DWZSquare.sameMarginalEntropyValues := by
  refine ⟨mme_modern_entropyBits MME.DWZSquare.alpha +
      2 * MME.DWZSquare.entropyEpsilon, ?_⟩
  intro h hh
  rcases hh with ⟨p, hp, hpsum, hmX, hmY, hmZ, rfl⟩
  exact mme_modern_entropyBits_additive_certificate
    MME.DWZSquare.shapeX MME.DWZSquare.shapeY MME.DWZSquare.shapeZ
    p MME.DWZSquare.alpha
    MME.DWZSquare.entropyLambdaZero
    MME.DWZSquare.entropyLambdaX
    MME.DWZSquare.entropyLambdaY
    MME.DWZSquare.entropyLambdaZ
    MME.DWZSquare.entropyEpsilon
    hp MME.DWZSquare.alpha_pos hpsum MME.DWZSquare.alpha_sum
    hmX hmY hmZ (by norm_num [MME.DWZSquare.entropyEpsilon])
    mme_dwz_table2_entropy_potential

end MME.DWZSameMarginalBdd

theorem solution :
    BddAbove MME.DWZSquare.sameMarginalEntropyValues :=
  MME.DWZSameMarginalBdd.proof
