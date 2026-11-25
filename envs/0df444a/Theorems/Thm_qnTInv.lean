-- Prove2me | Theorems.Thm_qnTInv
-- name    : qnTInv
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:31:43.860801+00:00
-- url     : https://prove2.me/theorems/3243a94b-70c4-4e01-9c69-94377c43b52b
-- title:
--   qn TInv: qn TInv
-- statement:
--   The qn TInv construction uses the qn TInv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnTInv.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QnTInv.lean#L10-L14

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TorusInvariance_QnTInvOf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnMinorLeft
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnEabPres
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnEabGl
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovLin
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovDet
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnCovHat
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CovariantHatSqOfLin
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QnTInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem qnTInv : Formalism.FourierDecayAlt.Q.TInvariant := by sorry
