-- Prove2me | Theorems.Thm_imag_quadratic_integral_basis
-- name    : imag_quadratic_integral_basis
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:23:54.395336+00:00
-- url     : https://prove2.me/theorems/4f092769-05cf-4a8b-b896-9eafe5d56fb5
-- title:
--   imag quadratic integral basis: imag quadratic integral basis
-- statement:
--   The imag quadratic integral basis construction uses the imag quadratic integral basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ClassNumImQInt.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/ClassNumImQInt.lean#L5-L6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ClassNumImQ
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ClassNumberIntegrality_HalfIntegral
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_ClassNumImQInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem imag_quadratic_integral_basis : PI.ClassNumImQ.IntBasis := by sorry
