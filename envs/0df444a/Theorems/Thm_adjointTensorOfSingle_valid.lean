-- Prove2me | Theorems.Thm_adjointTensorOfSingle_valid
-- name    : adjointTensorOfSingle_valid
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:14:19.480931+00:00
-- url     : https://prove2.me/theorems/73ea19d6-a303-4364-aac4-79299c30695a
-- title:
--   adjoint Tensor Of Single valid: adjoint Tensor Of Single valid
-- statement:
--   The adjoint Tensor Of Single valid construction uses the adjoint Tensor Of Single valid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/AdjointTensorOfSingleValid.lean#L9-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/AdjointTensorOfSingleValid.lean#L9-L11

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_FockRBlock
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_OkSmulRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_FilterConcatWLength
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_MultidegSingle
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_NotMemVarsEmbS
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_TensorOperator_StepMonoFactor
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_AdjointTensorOfSingleValid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem adjointTensorOfSingle_valid : PI.TenOp := by sorry
