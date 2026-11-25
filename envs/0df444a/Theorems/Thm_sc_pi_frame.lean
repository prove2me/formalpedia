-- Prove2me | Theorems.Thm_sc_pi_frame
-- name    : sc_pi_frame
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:18:11.575993+00:00
-- url     : https://prove2.me/theorems/d788fc9d-a0b8-4a32-ab24-08198850d89c
-- title:
--   sc pi frame: sc pi frame
-- statement:
--   The sc pi frame construction uses the sc pi frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ScPiFrame.lean#L6-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ScPiFrame.lean#L6-L6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_FrameHolds
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HermitianFrameExistence_FrameHypothesesRankZero
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ScPiFrame
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem sc_pi_frame : PI.ScPiExists.Frame := by sorry
