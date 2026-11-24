-- Prove2me | Theorems.Thm_contraction_adapted
-- name    : contraction_adapted
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:55:31.524904+00:00
-- url     : https://prove2.me/theorems/efb99076-0cdd-4b7e-b5d2-078a354e3367
-- title:
--   contraction adapted: contraction adapted
-- statement:
--   The contraction adapted construction uses the contraction adapted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnAdapted.lean#L5-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnAdapted.lean#L5-L7

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdaptedCharacterForm_SecondCapelliMinorStandardBasis
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnAdapted
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem contraction_adapted : Formalism.FourierDecayAlt.Q.ContractionsCovariant → Formalism.FourierDecayAlt.Q.ChatAdapted ∧ Formalism.FourierDecayAlt.Q.Chat2Adapted := by sorry
