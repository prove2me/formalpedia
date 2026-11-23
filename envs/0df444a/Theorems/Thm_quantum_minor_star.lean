-- Prove2me | Theorems.Thm_quantum_minor_star
-- name    : quantum_minor_star
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:05.814419+00:00
-- url     : https://prove2.me/theorems/3ef053f8-8f7e-4592-8ae8-270b622dd468
-- title:
--   quantum minor star: quantum minor star
-- statement:
--   The quantum minor star construction uses the quantum minor star property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QmStar.lean#L4-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QmStar.lean#L4-L5

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_IntegerProductCast_OfFnProdIntCast
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmRowForm
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmStar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem quantum_minor_star : PI.QmStar := by sorry
