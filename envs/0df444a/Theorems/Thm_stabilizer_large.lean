-- Prove2me | Theorems.Thm_stabilizer_large
-- name    : stabilizer_large
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:17:10.456452+00:00
-- url     : https://prove2.me/theorems/504ae8c6-ecd0-5385-969b-c4fa048bbca2
-- title:
--   stabilizer large: stabilizer large
-- statement:
--   The stabilizer large construction uses the stabilizer large property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/StabBig.lean#L5-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/StabBig.lean#L5-L5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_StabBig
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LargeStabilizerInverse_GLeftInv
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_StabBig
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem stabilizer_large : PI.StabBig := by sorry
