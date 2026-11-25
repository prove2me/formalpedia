-- Prove2me | Theorems.Thm_dual_difference
-- name    : dual_difference
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:15:46.391203+00:00
-- url     : https://prove2.me/theorems/a69bb488-f9ca-4d2f-afb9-22392fdadc68
-- title:
--   dual difference: dual difference
-- statement:
--   The dual difference construction uses the dual difference property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantTheorems/TBIdemDen.lean#L7-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/TaylorDiscriminants/DiscriminantEstimates/DiscriminantTheorems/TBIdemDen.lean#L7-L7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_IdemDen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_IdempotentEvaluation_IdemEval
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantLemmas_IdempotentEvaluation_DualDiff
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_TBIdemDen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem dual_difference : ReciprocityTheory.ChartRestriction.G.TB.DualDiffSt := by sorry
