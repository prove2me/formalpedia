-- Prove2me | Theorems.Thm_sc_psi_exists
-- name    : sc_psi_exists
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:17:13.415455+00:00
-- url     : https://prove2.me/theorems/111b72da-3d44-4da9-982f-7044666593bc
-- title:
--   sc psi exists: sc psi exists
-- statement:
--   The sc psi exists construction uses the sc psi exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ScPsiExists.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ScPsiExists.lean#L5-L6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScPsiExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_EmbeddingTraceSumAlt_NormUnitsOfCalculation
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ScPsiExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem sc_psi_exists : PI.ScPsiExists.Target := by sorry
