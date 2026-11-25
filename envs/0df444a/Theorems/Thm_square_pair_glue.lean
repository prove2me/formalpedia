-- Prove2me | Theorems.Thm_square_pair_glue
-- name    : square_pair_glue
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:16:45.049204+00:00
-- url     : https://prove2.me/theorems/9d8e8e42-5947-4348-a4eb-fb29d8c41dd9
-- title:
--   square pair glue: square pair glue
-- statement:
--   The square pair glue construction uses the square pair glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/SqPairGlue.lean#L4-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/SqPairGlue.lean#L4-L5

import Definitions.Def_Formalism_PeriodIntegrals_SqPair
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairGluing_SqPairGlueMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_SqPairGlue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem square_pair_glue : PI.SqPair.PLocalAll → Formalism.L2.PairingIndexBounds.Eq.SqG.SplitPairGen := by sorry
