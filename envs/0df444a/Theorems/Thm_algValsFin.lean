-- Prove2me | Theorems.Thm_algValsFin
-- name    : algValsFin
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:41:02.934027+00:00
-- url     : https://prove2.me/theorems/cbaa7f4b-270f-4831-b6e4-fe7c0e7534fb
-- title:
--   alg Vals Fin: alg Vals Fin
-- statement:
--   The alg Vals Fin construction uses the alg Vals Fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/AlgValsFin.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/AlgValsFin.lean#L8-L9

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

theorem algValsFin (L : Type) [Field L] [NumberField L] : PI.AlgValsFin.AlgValsFin L := by sorry
