-- Prove2me | solution 1 for mme_CW_support_pattern_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-31T18:06:26.49355+00:00
-- url     : https://prove2.me/submissions/60c091e1-0427-4c89-a464-99ed2d8b3161

import Definitions.Def_mme_CW_support_pattern
import Definitions.Def_mme_laser_pattern

open MME

theorem solution : LaserSymmetric CWSupportPattern := by
  intro x hx
  fin_cases hx <;> decide
