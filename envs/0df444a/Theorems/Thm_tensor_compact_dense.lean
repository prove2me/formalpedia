-- Prove2me | Theorems.Thm_tensor_compact_dense
-- name    : tensor_compact_dense
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:16:43.031826+00:00
-- url     : https://prove2.me/theorems/474daebc-cc0b-4283-a115-c805413590cf
-- title:
--   tensor compact dense: tensor compact dense
-- statement:
--   The tensor compact dense construction uses the tensor compact dense property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/TensCpctDen.lean#L6-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/TensCpctDen.lean#L6-L6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FinOrdAd
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AdCpctDen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactTensorDensity_TensCpctDenOf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TensCpctDen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem tensor_compact_dense : PI.TensCpctDen := by sorry
