-- Prove2me | Theorems.Thm_quantum_minor_move
-- name    : quantum_minor_move
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:11:27.686018+00:00
-- url     : https://prove2.me/theorems/63047254-9931-43c7-ae11-4597bd0a1d84
-- title:
--   quantum minor move: quantum minor move
-- statement:
--   The quantum minor move construction uses the quantum minor move property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QmMove.lean#L3-L3
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/QmMove.lean#L3-L3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CovariantVectorMove_SumPermsSignSquared
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_QmMove
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem quantum_minor_move : PI.QmMove := by sorry
