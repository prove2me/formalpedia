-- Prove2me | Theorems.Thm_isConvIdempotent_pi
-- name    : isConvIdempotent_pi
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:14:53.324795+00:00
-- url     : https://prove2.me/theorems/9abde913-2e02-4f73-9e9a-c8b4e783cc45
-- title:
--   is Conv Idempotent pi: is Conv Idempotent pi
-- statement:
--   The is Conv Idempotent pi construction uses the is Conv Idempotent pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/PhProdConv.lean#L4-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/PhProdConv.lean#L4-L28

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_PhProdConv
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PhProdConv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem isConvIdempotent_pi : PI.PhProdConv.ProdConv := by sorry
