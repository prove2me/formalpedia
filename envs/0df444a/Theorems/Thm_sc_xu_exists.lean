-- Prove2me | Theorems.Thm_sc_xu_exists
-- name    : sc_xu_exists
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:28:50.528238+00:00
-- url     : https://prove2.me/theorems/cb060c42-3b85-5192-a1fa-8bdb4514c722
-- title:
--   sc xu exists: sc xu exists
-- statement:
--   The sc xu exists construction uses the sc xu exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ScXuExists.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ScXuExists.lean#L8-L10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScXuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_Assemble
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SplitLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_LocalDataSatisfyLinearHypotheses
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeAutomorphismApprox_SplitUnitaryProjectionCompatibility
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ScXuExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem sc_xu_exists : PI.ScXuExists.Target := by sorry
