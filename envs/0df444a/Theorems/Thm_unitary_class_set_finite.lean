-- Prove2me | Theorems.Thm_unitary_class_set_finite
-- name    : unitary_class_set_finite
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T15:56:05.003799+00:00
-- url     : https://prove2.me/theorems/53708478-c8e1-4bdf-9d62-5eb1325cf9a2
-- title:
--   unitary class set finite: unitary class set finite
-- statement:
--   The unitary class set finite construction uses the unitary class set finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/UJClassFin.lean#L7-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/UJClassFin.lean#L7-L9

import Definitions.Def_Formalism_PeriodIntegrals_UJClassFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_UJClassFinOfLatFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_PosDefOfDefiniteSignatureHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_LatticeClassesFiniteRefinement
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassFiniteness_AdelicBounds
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UJClassFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem unitary_class_set_finite : PI.UJClassFin.UJClassFin := by sorry
