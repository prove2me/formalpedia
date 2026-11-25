-- Prove2me | Theorems.Thm_squarefree_roots_injective
-- name    : squarefree_roots_injective
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T11:17:16.026365+00:00
-- url     : https://prove2.me/theorems/2ece3c92-0ccb-4b48-bcd3-00817f30bdae
-- title:
--   squarefree roots injective: squarefree roots injective
-- statement:
--   The squarefree roots injective construction uses the squarefree roots injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/SqfRootsInj.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/SqfRootsInj.lean#L6-L7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SqfRootsInj
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_WitMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_RpowQuarterPowFour
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SqfRootsInj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem squarefree_roots_injective : PI.SqfRootsInj.Claim := by sorry
