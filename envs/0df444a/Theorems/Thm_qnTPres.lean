-- Prove2me | Theorems.Thm_qnTPres
-- name    : qnTPres
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:56:12.604283+00:00
-- url     : https://prove2.me/theorems/2b084e0b-b614-492c-8749-23f187f55609
-- title:
--   qn TPres: qn TPres
-- statement:
--   The qn TPres construction uses the qn TPres property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnTPres.lean#L4-L4
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnTPres.lean#L4-L4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinorSmoothness_SecondCapelliMinorContinuousLinear
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnTInv
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnTPres
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem qnTPres : Formalism.FourierDecayAlt.Q.TPreservesFF := by sorry
