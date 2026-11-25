-- Prove2me | Theorems.Thm_finiteAdeleIntegers_compactOpen
-- name    : finiteAdeleIntegers_compactOpen
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:14:34.764489+00:00
-- url     : https://prove2.me/theorems/f147ece7-8487-4e22-9982-94411f703991
-- title:
--   finite Adele Integers compact Open: finite Adele Integers compact Open
-- statement:
--   The finite Adele Integers compact Open construction uses the finite Adele Integers compact Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/IntAdCpctOpen.lean#L5-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/IntAdCpctOpen.lean#L5-L5

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_AdelicCompactOpens_IntAdelesCompactOpen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdicIntegersCompact_IsCompactAdicCompletionIntegers
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_IntAdCpctOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem finiteAdeleIntegers_compactOpen : Formalism.L2.Props.IntAdelesCompactOpen := by sorry
