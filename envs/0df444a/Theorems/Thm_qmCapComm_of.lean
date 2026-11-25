-- Prove2me | Theorems.Thm_qmCapComm_of
-- name    : qmCapComm_of
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:15:24.636469+00:00
-- url     : https://prove2.me/theorems/eff8d635-254a-4935-9d90-81a3ac1c60e6
-- title:
--   qm Cap Comm of: qm Cap Comm of
-- statement:
--   The qm Cap Comm of construction uses the qm Cap Comm of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QmCapComm.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QmCapComm.lean#L7-L8

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

theorem qmCapComm_of : Formalism.FourierDecayAlt.Q.EabPres → Formalism.FourierDecayAlt.Q.EabGlLev → Formalism.FourierDecayAlt.Q.CapCommute := by sorry
