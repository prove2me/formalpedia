-- Prove2me | Theorems.Thm_finite_order_adelic
-- name    : finite_order_adelic
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:15:03.200844+00:00
-- url     : https://prove2.me/theorems/f803d8b8-4d42-4ae3-88ca-52fbeec69909
-- title:
--   finite order adelic: finite order adelic
-- statement:
--   The finite order adelic construction uses the finite order adelic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/FinOrdAd.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/FinOrdAd.lean#L9-L10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FinOrdAd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicFiniteOrder_Assembly
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnitKron
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_PowBddInt
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_TensCpctDen
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DefPosDef
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FinOrdAd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem finite_order_adelic : PI.FinOrdAd := by sorry
