-- Prove2me | Theorems.Thm_modelIso_of
-- name    : modelIso_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:25:24.741093+00:00
-- url     : https://prove2.me/theorems/96fab42b-8331-4fcf-9ab2-e91e4b417b7e
-- title:
--   model Iso of: model Iso of
-- statement:
--   The model Iso of construction uses the model Iso of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ModelIso.lean#L8-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ModelIso.lean#L8-L10

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_Assembly
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_PolyExt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_TorusEigenvalueFormula
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_ModelMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialModelIsometry_DetSplit
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_HwIrred
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ModelIso
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem modelIso_of : PI.PolyCoef → PI.UnitaryDense → PI.HwIrred → PI.ModelIso := by sorry
