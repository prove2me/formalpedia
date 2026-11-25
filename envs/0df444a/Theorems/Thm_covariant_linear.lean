-- Prove2me | Theorems.Thm_covariant_linear
-- name    : covariant_linear
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:24:03.656137+00:00
-- url     : https://prove2.me/theorems/eb6333ee-b985-4f72-819d-87ef617e4471
-- title:
--   covariant linear: covariant linear
-- statement:
--   The covariant linear construction uses the covariant linear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnCovLin.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnCovLin.lean#L5-L6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantLinearProduct_OfFnProdSmul
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovLin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem covariant_linear : PI.QnCovLin := by sorry
