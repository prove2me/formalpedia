-- Prove2me | Theorems.Thm_jets_high
-- name    : jets_high
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:15:12.21432+00:00
-- url     : https://prove2.me/theorems/7afabe9f-8e88-497c-b7a8-bd5286967a50
-- title:
--   jets high: jets high
-- statement:
--   The jets high construction uses the jets high property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/JetsPhW.lean#L17-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/JetsPhW.lean#L17-L18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_GlueHoldsVar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_HighGOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_ChainSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_InvOmega
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_FirstJetIntegralGeneralHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_JetIntegrality_SecondJetIntegralGeneralHolds
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_JetsPhW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem jets_high : PI.JetsPhW.High := by sorry
