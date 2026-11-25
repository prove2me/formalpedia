-- Prove2me | Theorems.Thm_scGapBig
-- name    : scGapBig
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:17:01.437789+00:00
-- url     : https://prove2.me/theorems/e67e3d18-7d58-4f54-8516-a3115a6901b9
-- title:
--   sc Gap Big: sc Gap Big
-- statement:
--   The sc Gap Big construction uses the sc Gap Big property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ScGapBig.lean#L5-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ScGapBig.lean#L5-L5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScGapBig
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SpectralGapLarge_ScGapBigMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ScGapBig
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem scGapBig : PI.ScGapBig.ScGapBig := by sorry
