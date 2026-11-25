-- Prove2me | Theorems.Thm_algebraic_values_finite
-- name    : algebraic_values_finite
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:40:57.303573+00:00
-- url     : https://prove2.me/theorems/f3b497a3-b483-4e4d-97af-a6479abe8ed2
-- title:
--   algebraic values finite: algebraic values finite
-- statement:
--   The algebraic values finite construction uses the algebraic values finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/AlgValsFin.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/AlgValsFin.lean#L5-L6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AlgValsFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AlgebraicValuesFinite_AlgValsFinMain
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AlgValsFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem algebraic_values_finite (L : Type) [Field L] [NumberField L] : PI.AlgValsFin.AlgValsFin L := by sorry
