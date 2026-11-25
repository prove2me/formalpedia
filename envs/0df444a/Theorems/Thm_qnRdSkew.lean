-- Prove2me | Theorems.Thm_qnRdSkew
-- name    : qnRdSkew
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:02:55.062646+00:00
-- url     : https://prove2.me/theorems/99d564d1-9056-4df8-bad7-fcf79ab04c94
-- title:
--   qn Rd Skew: qn Rd Skew
-- statement:
--   The qn Rd Skew construction uses the qn Rd Skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnRdSkew.lean#L4-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnRdSkew.lean#L4-L5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_SkewReductionGroup
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SkewAnalyticGroup_Analytic
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnRdSkew
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem qnRdSkew : Formalism.FourierDecayAlt.Q.RdSkew := by sorry
