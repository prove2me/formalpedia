-- Prove2me | Theorems.Thm_low_smooth_of_k_finite
-- name    : low_smooth_of_k_finite
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:14:13.586706+00:00
-- url     : https://prove2.me/theorems/ab3bc055-2788-444c-a912-829265640d49
-- title:
--   low smooth of k finite: low smooth of k finite
-- statement:
--   The low smooth of k finite construction uses the low smooth of k finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/LowSmooth.lean#L6-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/LowSmooth.lean#L6-L6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LowCyc
import Definitions.Def_Formalism_PeriodIntegrals_KFinSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerSmoothStability_ExistsFinStableOfMemSSup
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LowSmooth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem low_smooth_of_k_finite : PI.KFinSmooth → PI.LowSmooth := by sorry
