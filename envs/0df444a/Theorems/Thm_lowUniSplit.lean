-- Prove2me | Theorems.Thm_lowUniSplit
-- name    : lowUniSplit
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:14:43.24714+00:00
-- url     : https://prove2.me/theorems/4612d76d-035c-4c94-912c-cfcdede76794
-- title:
--   low Uni Split: low Uni Split
-- statement:
--   The low Uni Split construction uses the low Uni Split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/LowUniSplit.lean#L3-L3
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/LowUniSplit.lean#L3-L3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LowerUnipotentSplit_SecondFactorMemLowerTriangular
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_LowUniSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem lowUniSplit : Formalism.FourierDecayAlt.C2.LowSplit := by sorry
