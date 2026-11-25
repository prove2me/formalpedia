-- Prove2me | Theorems.Thm_kernel_split_of_jacobi
-- name    : kernel_split_of_jacobi
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:54:17.922802+00:00
-- url     : https://prove2.me/theorems/94541cd2-7a9d-4c80-ae3c-b03167153531
-- title:
--   kernel split of jacobi: kernel split of jacobi
-- statement:
--   The kernel split of jacobi construction uses the kernel split of jacobi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/KerSplit.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/KerSplit.lean#L5-L10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualOfDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KernelSplitting_IsIntegralHalf
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_KerSplit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem kernel_split_of_jacobi : PI.KerIso.SplitOfJacobi := by sorry
