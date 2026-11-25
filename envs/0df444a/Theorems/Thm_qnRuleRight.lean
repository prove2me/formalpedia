-- Prove2me | Theorems.Thm_qnRuleRight
-- name    : qnRuleRight
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:15:34.094619+00:00
-- url     : https://prove2.me/theorems/731a42e0-d0b7-48a1-96b2-41bf1f15889b
-- title:
--   qn Rule Right: qn Rule Right
-- statement:
--   The qn Rule Right construction uses the qn Rule Right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnRuleRight.lean#L3-L3
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnRuleRight.lean#L3-L3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_RightSingleRule_EllSingleZero
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnRuleRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem qnRuleRight : Formalism.FourierDecayAlt.Q.RuleRight := by sorry
