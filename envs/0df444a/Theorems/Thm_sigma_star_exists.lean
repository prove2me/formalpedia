-- Prove2me | Theorems.Thm_sigma_star_exists
-- name    : sigma_star_exists
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:17:49.655125+00:00
-- url     : https://prove2.me/theorems/a89d42f5-0be8-486c-a853-cf30f7e8ed32
-- title:
--   sigma star exists: sigma star exists
-- statement:
--   The sigma star exists construction uses the sigma star exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/SigmaStarEx.lean#L6-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/SigmaStarEx.lean#L6-L6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatDefs
import Definitions.Def_Formalism_PeriodIntegrals_SigmaStarEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ThetaSeriesExistence_SigmaStarEx
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SigmaStarEx
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem sigma_star_exists : PI.SigmaStarEx := by sorry
