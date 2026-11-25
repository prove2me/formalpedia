-- Prove2me | Theorems.Thm_adelic_class_set_finite
-- name    : adelic_class_set_finite
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T11:17:30.710311+00:00
-- url     : https://prove2.me/theorems/536bc848-2eb7-4b99-b179-6e9e04ef862d
-- title:
--   adelic class set finite: adelic class set finite
-- statement:
--   The adelic class set finite construction uses the adelic class set finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/AdelClassFin.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/AdelClassFin.lean#L5-L6

import Definitions.Def_Formalism_PeriodIntegrals_AdelClassFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_AdelClassFinOfSvReal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_SuccessiveVectorReal
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AdelClassFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem adelic_class_set_finite : PI.AdelClassFin.AdelClassFin := by sorry
