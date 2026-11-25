-- Prove2me | Theorems.Thm_sc_reference_exists
-- name    : sc_reference_exists
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:18:14.180465+00:00
-- url     : https://prove2.me/theorems/5b28adab-0dba-4ae8-a6ca-10fda3712a15
-- title:
--   sc reference exists: sc reference exists
-- statement:
--   The sc reference exists construction uses the sc reference exists property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ScRefExists.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ScRefExists.lean#L8-L10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScRefExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_TargetOfWframe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WFrameOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_PrincipalIdealRingAtPrime
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LatticeReferenceFrame_WeilBasisExistence
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ScRefExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem sc_reference_exists : PI.ScRefExists.Target := by sorry
