-- Prove2me | Theorems.Thm_gelfCpt_closed
-- name    : gelfCpt_closed
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:15:02.119018+00:00
-- url     : https://prove2.me/theorems/ebcfa452-3991-44ae-a2ef-c9948c92abc2
-- title:
--   gelf Cpt closed: gelf Cpt closed
-- statement:
--   The gelf Cpt closed construction uses the gelf Cpt closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ExplicitFormulaCounts/UMultOne.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ExplicitFormulaCounts/UMultOne.lean#L8-L9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitarySecondCountable_Assembly
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_GelfCptOf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_GelfSpan
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_GelfConv
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UConjT
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CommMult
import Definitions.Def_Formalism_PeriodIntegrals_ExplicitFormulaCounts_UMultOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem gelfCpt_closed : PI.UMultOne.GelfandCompact := by sorry
