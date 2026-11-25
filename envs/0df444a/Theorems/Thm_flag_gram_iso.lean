-- Prove2me | Theorems.Thm_flag_gram_iso
-- name    : flag_gram_iso
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:14:29.62141+00:00
-- url     : https://prove2.me/theorems/abde8b35-02e8-4b97-8845-5e2b37d1b03b
-- title:
--   flag gram iso: flag gram iso
-- statement:
--   The flag gram iso construction uses the flag gram iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/GramIso.lean#L5-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/GramIso.lean#L5-L5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FglGram
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramIsometryCoefficient_ExCoeffOneNe
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_GramIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem flag_gram_iso : PI.FglGram.GramIso := by sorry
