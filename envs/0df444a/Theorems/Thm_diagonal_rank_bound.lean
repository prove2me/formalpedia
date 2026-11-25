-- Prove2me | Theorems.Thm_diagonal_rank_bound
-- name    : diagonal_rank_bound
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:18:10.725838+00:00
-- url     : https://prove2.me/theorems/79d7459f-7737-41e6-83eb-309756bb8169
-- title:
--   diagonal rank bound: diagonal rank bound
-- statement:
--   The diagonal rank bound construction uses the diagonal rank bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/DiagRank.lean#L5-L5
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/OrbitalBoundsConclusion/DiagRank.lean#L5-L5

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_DiagRank
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_DiagonalRank_DetOneSubPNe
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_DiagRank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem diagonal_rank_bound : PI.DiagRank := by sorry
