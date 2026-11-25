-- Prove2me | Theorems.Thm_covariant_hat_sq_of_lin
-- name    : covariant_hat_sq_of_lin
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:03:11.651541+00:00
-- url     : https://prove2.me/theorems/e20e2775-b00a-49d4-9cb2-260dcc0fa329
-- title:
--   covariant hat sq of lin: covariant hat sq of lin
-- statement:
--   The covariant hat sq of lin construction uses the covariant hat sq of lin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/CovariantHatSqOfLin.lean#L5-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/CovariantHatSqOfLin.lean#L5-L5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantHatPairReindex_QnCovHat2OfLin
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CovariantHatSqOfLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem covariant_hat_sq_of_lin : PI.QnCovLin → PI.QnCovHat2 := by sorry
