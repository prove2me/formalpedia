-- Prove2me | Theorems.Thm_qmCapComm_of_gl
-- name    : qmCapComm_of_gl
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:16:18.30831+00:00
-- url     : https://prove2.me/theorems/71ea6544-3b83-4667-a61e-7ae2d740b080
-- title:
--   qm Cap Comm of gl: qm Cap Comm of gl
-- statement:
--   The qm Cap Comm of gl construction uses the qm Cap Comm of gl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QmCapComm.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QmCapComm.lean#L10-L11

import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnEabGl
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnEabPres
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_Transfer
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_CapelliOperatorCongruence
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuantumDeterminantCommute_QuantumDeterminantCommutes
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmCapComm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem qmCapComm_of_gl : Formalism.FourierDecayAlt.Q.EabGlLev → Formalism.FourierDecayAlt.Q.CapCommute := by sorry
