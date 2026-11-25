-- Prove2me | Theorems.Thm_jets_two
-- name    : jets_two
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:15:34.484254+00:00
-- url     : https://prove2.me/theorems/deb2ed7f-6b63-46e0-8717-96845a78ae95
-- title:
--   jets two: jets two
-- statement:
--   The jets two construction uses the jets two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/JetsPhW.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/JetsPhW.lean#L23-L24

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

theorem jets_two : PI.JetsPhW.Two := by sorry
