-- Prove2me | Theorems.Thm_symDist_of
-- name    : symDist_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:16:33.267026+00:00
-- url     : https://prove2.me/theorems/4da4ed5d-6889-466f-9d37-9d345c902ce2
-- title:
--   sym Dist of: sym Dist of
-- statement:
--   The sym Dist of construction uses the sym Dist of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/SymDist.lean#L6-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/SymDist.lean#L6-L6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SymDist
import Definitions.Def_Formalism_PeriodIntegrals_ExpTri
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SymmetricDistance_SymDistOf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SymDist
import Theorems.Thm_PI_SymDistWork_symDist_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem symDist_of : PI.ExpTri → PI.SymDist := by sorry
