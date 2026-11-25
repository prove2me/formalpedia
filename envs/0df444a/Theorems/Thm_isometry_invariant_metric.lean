-- Prove2me | Theorems.Thm_isometry_invariant_metric
-- name    : isometry_invariant_metric
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:15:29.485591+00:00
-- url     : https://prove2.me/theorems/08a17c3a-2f6a-4f39-b64d-458e1c491d92
-- title:
--   isometry invariant metric: isometry invariant metric
-- statement:
--   The isometry invariant metric construction uses the isometry invariant metric property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/IsoInvMetric.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/IsoInvMetric.lean#L6-L7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_IsoInvMetric
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_IsoInvMetricOfHw
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_PolyEqZeroOfCircle
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IsoInvMetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem isometry_invariant_metric : PI.IsoInvMetric.IsoInvMetric := by sorry
