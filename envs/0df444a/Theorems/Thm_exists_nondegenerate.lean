-- Prove2me | Theorems.Thm_exists_nondegenerate
-- name    : exists_nondegenerate
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:27.93445+00:00
-- url     : https://prove2.me/theorems/e2b765de-538d-49c6-850c-3a6e15236de2
-- title:
--   exists nondegenerate: exists nondegenerate
-- statement:
--   The exists nondegenerate construction uses the exists nondegenerate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/NormGramAtOrigin.lean#L154-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/NormGramAtOrigin.lean#L154-L171

import Definitions.Def_Formalism_PeriodIntegrals_NormGramAtOrigin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OrthogonalFamilyExistence_ExistsOrthFamily
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_NormGramAtOrigin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem exists_nondegenerate : PI.NormGramAtOrigin.Statement := by sorry
