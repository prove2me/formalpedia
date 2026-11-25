-- Prove2me | Theorems.Thm_kernel_tensor_spans
-- name    : kernel_tensor_spans
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T11:15:57.626521+00:00
-- url     : https://prove2.me/theorems/1daa6a04-2efd-4189-8c05-1f6f779ba971
-- title:
--   kernel tensor spans: kernel tensor spans
-- statement:
--   The kernel tensor spans construction uses the kernel tensor spans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/KerTens.lean#L5-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/KerTens.lean#L5-L5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerTens
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorSpanning_TensSpans
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_KerTens
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem kernel_tensor_spans : PI.KerTens.TensSpans := by sorry
