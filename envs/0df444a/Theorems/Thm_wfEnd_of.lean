-- Prove2me | Theorems.Thm_wfEnd_of
-- name    : wfEnd_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:04:30.613731+00:00
-- url     : https://prove2.me/theorems/e2f120f8-eecd-566f-80a2-c53510cb520d
-- title:
--   wf End of: wf End of
-- statement:
--   The wf End of construction uses the wf End of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/WittFrobeniusEnd.lean#L8-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/WittFrobeniusEnd.lean#L8-L8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittEndomorphism_WfEndOfLog
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittLogarithm
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WittFrobeniusEnd
import Theorems.Thm_PI_WfEndProof_wfEnd_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem wfEnd_of : PI.WfRing → PI.WfSubst → PI.WfLog → PI.WfEnd := by sorry
