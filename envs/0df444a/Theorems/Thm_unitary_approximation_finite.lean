-- Prove2me | Theorems.Thm_unitary_approximation_finite
-- name    : unitary_approximation_finite
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:24:40.737665+00:00
-- url     : https://prove2.me/theorems/145d664a-92fa-44b1-b688-1e689fb09c1f
-- title:
--   unitary approximation finite: unitary approximation finite
-- statement:
--   The unitary approximation finite construction uses the unitary approximation finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/UnitaryApproxFin.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/UnitaryApproxFin.lean#L12-L16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApprox
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApproxFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_TopStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_Assembly
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_ApproxE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproximationFiniteUnitary
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_BoundedRationalUnitary
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_UnitaryScalars
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_EigenvalueAvoidance
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_UnitaryApproxFin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem unitary_approximation_finite : PI.UnitaryApproxFin.UnitaryApproxFin := by sorry
