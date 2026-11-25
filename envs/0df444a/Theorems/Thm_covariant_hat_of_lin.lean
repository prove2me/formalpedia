-- Prove2me | Theorems.Thm_covariant_hat_of_lin
-- name    : covariant_hat_of_lin
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:27:19.16891+00:00
-- url     : https://prove2.me/theorems/153d0120-d1b0-4904-8b36-734dfe99fdfd
-- title:
--   covariant hat of lin: covariant hat of lin
-- statement:
--   The covariant hat of lin construction uses the covariant hat of lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnCovHat.lean#L3-L4
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnCovHat.lean#L3-L4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatDecomposition_SkipOneEqSuccAbove
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovHat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem covariant_hat_of_lin : PI.QnCovLin → PI.QnCovHat := by sorry
