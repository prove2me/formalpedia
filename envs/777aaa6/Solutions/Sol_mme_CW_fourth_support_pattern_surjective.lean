-- Prove2me | solution 1 for mme_CW_fourth_support_pattern_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T19:43:58.683175+00:00
-- url     : https://prove2.me/submissions/874bc01a-ff65-431d-9042-a6a6ea62917b

import Definitions.Def_mme_CW_fourth_support_patterns

open BigOperators

namespace MME.StothersFourth

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

/-- A fixed witness for each of the 45 ordered triples of total degree eight. -/
private def canonicalFourSupportWitness
    (sigma : Fin 3 → Fin 9) : Fin 4 → Fin 6 :=
  if sigma = ![0, 0, 8] then ![3, 3, 3, 3] else
  if sigma = ![0, 1, 7] then ![0, 3, 3, 3] else
  if sigma = ![0, 2, 6] then ![0, 0, 3, 3] else
  if sigma = ![0, 3, 5] then ![0, 0, 0, 3] else
  if sigma = ![0, 4, 4] then ![0, 0, 0, 0] else
  if sigma = ![0, 5, 3] then ![0, 0, 0, 4] else
  if sigma = ![0, 6, 2] then ![0, 0, 4, 4] else
  if sigma = ![0, 7, 1] then ![0, 4, 4, 4] else
  if sigma = ![0, 8, 0] then ![4, 4, 4, 4] else
  if sigma = ![1, 0, 7] then ![1, 3, 3, 3] else
  if sigma = ![1, 1, 6] then ![0, 1, 3, 3] else
  if sigma = ![1, 2, 5] then ![0, 0, 1, 3] else
  if sigma = ![1, 3, 4] then ![0, 0, 0, 1] else
  if sigma = ![1, 4, 3] then ![0, 0, 0, 2] else
  if sigma = ![1, 5, 2] then ![0, 0, 2, 4] else
  if sigma = ![1, 6, 1] then ![0, 2, 4, 4] else
  if sigma = ![1, 7, 0] then ![2, 4, 4, 4] else
  if sigma = ![2, 0, 6] then ![1, 1, 3, 3] else
  if sigma = ![2, 1, 5] then ![0, 1, 1, 3] else
  if sigma = ![2, 2, 4] then ![0, 0, 1, 1] else
  if sigma = ![2, 3, 3] then ![0, 0, 0, 5] else
  if sigma = ![2, 4, 2] then ![0, 0, 2, 2] else
  if sigma = ![2, 5, 1] then ![0, 2, 2, 4] else
  if sigma = ![2, 6, 0] then ![2, 2, 4, 4] else
  if sigma = ![3, 0, 5] then ![1, 1, 1, 3] else
  if sigma = ![3, 1, 4] then ![0, 1, 1, 1] else
  if sigma = ![3, 2, 3] then ![0, 0, 1, 5] else
  if sigma = ![3, 3, 2] then ![0, 0, 2, 5] else
  if sigma = ![3, 4, 1] then ![0, 2, 2, 2] else
  if sigma = ![3, 5, 0] then ![2, 2, 2, 4] else
  if sigma = ![4, 0, 4] then ![1, 1, 1, 1] else
  if sigma = ![4, 1, 3] then ![0, 1, 1, 5] else
  if sigma = ![4, 2, 2] then ![0, 0, 5, 5] else
  if sigma = ![4, 3, 1] then ![0, 2, 2, 5] else
  if sigma = ![4, 4, 0] then ![2, 2, 2, 2] else
  if sigma = ![5, 0, 3] then ![1, 1, 1, 5] else
  if sigma = ![5, 1, 2] then ![0, 1, 5, 5] else
  if sigma = ![5, 2, 1] then ![0, 2, 5, 5] else
  if sigma = ![5, 3, 0] then ![2, 2, 2, 5] else
  if sigma = ![6, 0, 2] then ![1, 1, 5, 5] else
  if sigma = ![6, 1, 1] then ![0, 5, 5, 5] else
  if sigma = ![6, 2, 0] then ![2, 2, 5, 5] else
  if sigma = ![7, 0, 1] then ![1, 5, 5, 5] else
  if sigma = ![7, 1, 0] then ![2, 5, 5, 5] else
  ![5, 5, 5, 5]

end MME.StothersFourth

set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

/-- Every ordered triple of grades summing to eight is a sum of four
single-CW support patterns. -/
theorem solution
    (sigma : Fin 3 → Fin 9)
    (hsum : (∑ s, (sigma s).val) = 8) :
    ∃ r : Fin 4 → Fin 6,
      ∀ s, MME.StothersFourth.cwFourSupportNatAddress r s =
        (sigma s).val := by
  refine ⟨MME.StothersFourth.canonicalFourSupportWitness sigma, ?_⟩
  revert sigma
  decide
