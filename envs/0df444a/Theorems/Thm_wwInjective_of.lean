-- Prove2me | Theorems.Thm_wwInjective_of
-- name    : wwInjective_of
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T11:55:17.067215+00:00
-- url     : https://prove2.me/theorems/0d943ef4-7731-5dd2-9750-0734a975823d
-- title:
--   ww Injective of: ww Injective of
-- statement:
--   The ww Injective of construction uses the ww Injective of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/WwInjective.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/WwInjective.lean#L6-L7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwInjective
import Definitions.Def_Formalism_PeriodIntegrals_WwCauchyBinet
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_GramInjectivity_InstFintypeColChoice
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_WwInjective
import Theorems.Thm_PI_WwInjectiveWork_wwInjective_of

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem wwInjective_of (h : PI.WwCauchyBinet.WwCauchyBinet) : PI.WwInjective.WwInjective := by sorry
