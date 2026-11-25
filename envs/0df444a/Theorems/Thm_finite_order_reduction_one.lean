-- Prove2me | Theorems.Thm_finite_order_reduction_one
-- name    : finite_order_reduction_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:35.076982+00:00
-- url     : https://prove2.me/theorems/0145e5a2-8f72-40f8-80a5-743c6463674b
-- title:
--   finite order reduction one: finite order reduction one
-- statement:
--   The finite order reduction one construction uses the finite order reduction one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/FinOrdRedOne.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/FinOrdRedOne.lean#L8-L11

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FinOrdRedOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_EqOneOfIsOfFinOrder
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FiniteOrderReduction_Bridge
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FinOrdRedOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain PI.FinOrdRedOne

theorem finite_order_reduction_one : PI.FinOrdRedOne := by sorry
