-- Prove2me | Theorems.Thm_ordRelativeDet_finite
-- name    : ordRelativeDet_finite
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:14:55.566278+00:00
-- url     : https://prove2.me/theorems/f62394da-c4e3-4766-94db-11976eab4b8f
-- title:
--   ord Relative Det finite: ord Relative Det finite
-- statement:
--   The ord Relative Det finite construction uses the ord Relative Det finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/KerDetFin.lean#L5-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/KerDetFin.lean#L5-L5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DeterminantKernelFiniteness_ExistsDenomBackward
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_KerDetFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem ordRelativeDet_finite : PI.KerIso.DetOrdFin := by sorry
