-- Prove2me | Theorems.Thm_chk_lBoundRight
-- name    : chk_lBoundRight
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:23:47.71557+00:00
-- url     : https://prove2.me/theorems/633bbd2a-27fd-443e-a300-b536a543394b
-- title:
--   chk l Bound Right: chk l Bound Right
-- statement:
--   The chk l Bound Right construction uses the chk l Bound Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ExplicitFormulaCounts/AnalyticInputs.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ExplicitFormulaCounts/AnalyticInputs.lean#L15-L24

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

theorem chk_lBoundRight : PI.LBoundRight := by sorry
