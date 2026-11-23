-- Prove2me | Theorems.Thm_highest_weight_irreducible
-- name    : highest_weight_irreducible
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:03:18.358449+00:00
-- url     : https://prove2.me/theorems/81c31ae9-41fb-4525-9358-f775d61f160a
-- title:
--   highest weight irreducible: highest weight irreducible
-- statement:
--   The highest weight irreducible construction uses the highest weight irreducible property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/HwIrred.lean#L5-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/HwIrred.lean#L5-L7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_Assembly
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightIrreducible_ConstructionB
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HwIrred
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem highest_weight_irreducible : PI.HwIrred := by sorry
