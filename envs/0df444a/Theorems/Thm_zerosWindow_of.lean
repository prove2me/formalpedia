-- Prove2me | Theorems.Thm_zerosWindow_of
-- name    : zerosWindow_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:16:09.8788+00:00
-- url     : https://prove2.me/theorems/95854bc7-2b05-5797-9cbe-d6856c463175
-- title:
--   zeros Window of: zeros Window of
-- statement:
--   The zeros Window of construction uses the zeros Window of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ZerosWindow.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ZerosWindow.lean#L7-L8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindow
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Transfer
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ZerosWindow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem zerosWindow_of : PI.LBoundRight → PI.ZetaBoundRight → PI.LInvRight → PI.ZerosWindow := by sorry
