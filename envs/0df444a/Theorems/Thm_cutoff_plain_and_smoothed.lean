-- Prove2me | Theorems.Thm_cutoff_plain_and_smoothed
-- name    : cutoff_plain_and_smoothed
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:09:59.014088+00:00
-- url     : https://prove2.me/theorems/027cc594-9ffe-4e52-bf7a-59983176d35f
-- title:
--   cutoff plain and smoothed: cutoff plain and smoothed
-- statement:
--   The cutoff plain and smoothed construction uses the cutoff plain and smoothed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/CutoffPlainAndSmoothed.lean#L3-L3
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/CutoffPlainAndSmoothed.lean#L3-L3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnipotentCorrectionU1_UnitaryCorollaryBothForms
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CutoffPlainAndSmoothed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem cutoff_plain_and_smoothed : Formalism.FourierDecayAlt.U.StarBoundOfCutoffOperator ∧ Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator := by sorry
