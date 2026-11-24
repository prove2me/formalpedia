-- Prove2me | Theorems.Thm_qnMinorLeft
-- name    : qnMinorLeft
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T15:55:41.121958+00:00
-- url     : https://prove2.me/theorems/9036fc21-fdaf-4c5b-a9f5-e5f9566a5e31
-- title:
--   qn Minor Left: qn Minor Left
-- statement:
--   The qn Minor Left construction uses the qn Minor Left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnMinorLeft.lean#L28-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnMinorLeft.lean#L28-L39

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LeftQuantumMinor_QuantumMinorLeftHermitian
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnMinorLeft
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem qnMinorLeft : Formalism.FourierDecayAlt.Q.QMinorLeftH := by sorry
