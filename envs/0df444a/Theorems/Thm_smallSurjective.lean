-- Prove2me | Theorems.Thm_smallSurjective
-- name    : smallSurjective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:16:50.648965+00:00
-- url     : https://prove2.me/theorems/d560f0d6-1f73-4a9c-9c8f-6d10f9f538e6
-- title:
--   small Surjective: small Surjective
-- statement:
--   The small Surjective construction uses the small Surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ASSmall.lean#L5-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ASSmall.lean#L5-L5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ArtSch
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SmallArtinSchreier_ExistsAsOfValLtOne
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ASSmall
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem smallSurjective : PI.ArtSch.TiltSmall := by sorry
