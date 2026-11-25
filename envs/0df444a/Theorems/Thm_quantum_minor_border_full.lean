-- Prove2me | Theorems.Thm_quantum_minor_border_full
-- name    : quantum_minor_border_full
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:14:24.805504+00:00
-- url     : https://prove2.me/theorems/3470ca60-9c07-5808-a5c7-971651d6da25
-- title:
--   quantum minor border full: quantum minor border full
-- statement:
--   The quantum minor border full construction uses the quantum minor border full property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QmBorderFull.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QmBorderFull.lean#L7-L8

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_QmBorderFullOf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmBorderES
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmColExp
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmRowExp
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmSkip
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmBorderFull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem quantum_minor_border_full : PI.QmBorderFull := by sorry
