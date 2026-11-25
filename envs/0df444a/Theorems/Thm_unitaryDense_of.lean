-- Prove2me | Theorems.Thm_unitaryDense_of
-- name    : unitaryDense_of
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T11:16:22.328399+00:00
-- url     : https://prove2.me/theorems/8c847667-0bf4-5ab8-89bc-a8b9012ad870
-- title:
--   unitary Dense of: unitary Dense of
-- statement:
--   The unitary Dense of construction uses the unitary Dense of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryDensity/Derived.lean#L23-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/UnitaryDensity/Derived.lean#L23-L32

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryDense
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryDensity_Derived
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MvPolynomial
open scoped ComplexOrder
open PI.UnitaryDenseWork

theorem unitaryDense_of (h : PI.FramesDense) : PI.UnitaryDense := by sorry
