-- Prove2me | Theorems.Thm_chk_lInvRight
-- name    : chk_lInvRight
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:23:47.31511+00:00
-- url     : https://prove2.me/theorems/0db5eebc-7039-476e-85db-1be995252f6d
-- title:
--   chk l Inv Right: chk l Inv Right
-- statement:
--   The chk l Inv Right construction uses the chk l Inv Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ExplicitFormulaCounts/AnalyticInputs.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ExplicitFormulaCounts/AnalyticInputs.lean#L13-L13

import Definitions.Def_Formalism_PeriodIntegrals_DiscIn
import Definitions.Def_Formalism_PeriodIntegrals_ZerosWindowIn
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LandauLocal3
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LGrowth
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_LRight
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_ZetaGrowth
import Definitions.Def_Formalism_PeriodIntegrals_ExplicitFormulaCounts_AnalyticInputs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem chk_lInvRight : PI.LInvRight := by sorry
