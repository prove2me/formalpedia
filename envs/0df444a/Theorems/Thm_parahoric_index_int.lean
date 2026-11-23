-- Prove2me | Theorems.Thm_parahoric_index_int
-- name    : parahoric_index_int
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:23:55.394678+00:00
-- url     : https://prove2.me/theorems/212b93d2-8662-46b7-b5c6-8d131c2df187
-- title:
--   parahoric index int: parahoric index int
-- statement:
--   The parahoric index int construction uses the parahoric index int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ParahoricIdxZ.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ParahoricIdxZ.lean#L7-L8

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ParahoricIdxZ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_SpanIsMaximal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_IdxStep
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ParahoricIdxZ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem parahoric_index_int : PI.ParahoricIdxZ := by sorry
