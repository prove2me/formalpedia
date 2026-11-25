-- Prove2me | Theorems.Thm_kernel_four_squares
-- name    : kernel_four_squares
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:50:38.185631+00:00
-- url     : https://prove2.me/theorems/d4673e87-8fd7-4d26-acaa-40e638d74815
-- title:
--   kernel four squares: kernel four squares
-- statement:
--   The kernel four squares construction uses the kernel four squares property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/KerFourSq.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/KerFourSq.lean#L5-L6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_KerIso
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FourSquareQuaternions_FourSqOfFromDiag
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_KerFourSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem kernel_four_squares : PI.KerIso.FourSq := by sorry
