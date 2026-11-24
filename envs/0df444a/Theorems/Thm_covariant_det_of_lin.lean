-- Prove2me | Theorems.Thm_covariant_det_of_lin
-- name    : covariant_det_of_lin
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T15:45:40.582036+00:00
-- url     : https://prove2.me/theorems/d53af01c-90cd-4ae5-a345-8fff845cb4ac
-- title:
--   covariant det of lin: covariant det of lin
-- statement:
--   The covariant det of lin construction uses the covariant det of lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnCovDet.lean#L3-L4
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnCovDet.lean#L3-L4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantDeterminantScaling_IntCastMulEqSmul
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem covariant_det_of_lin : PI.QnCovLin → PI.QnCovDet := by sorry
