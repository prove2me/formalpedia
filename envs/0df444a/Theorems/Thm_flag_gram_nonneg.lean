-- Prove2me | Theorems.Thm_flag_gram_nonneg
-- name    : flag_gram_nonneg
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:14:37.837348+00:00
-- url     : https://prove2.me/theorems/988a53e9-d48c-44ae-a0e9-908d219a8ba0
-- title:
--   flag gram nonneg: flag gram nonneg
-- statement:
--   The flag gram nonneg construction uses the flag gram nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/FlagGramNonneg.lean#L5-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/FlagGramNonneg.lean#L5-L5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FlagGramNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FlagGramNonnegativity_Gval
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FlagGramNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem flag_gram_nonneg : PI.FlagGramNonneg := by sorry
