-- Prove2me | Theorems.Thm_lowerSum_le_of_refinement
-- name    : lowerSum_le_of_refinement
-- status  : Open
-- author  : @WillR
-- created : 2026-11-12T22:53:22.018583+00:00
-- url     : https://prove2.me/theorems/343e82e7-3c04-4d38-8584-4eb391e2abf8
-- title:
--   Chapter 1, thm_1_2: lowerSum_le_of_refinement
-- statement:
--   Source theorem `lowerSum_le_of_refinement` from Chapter 1, module `thm_1_2`. Its exact formal statement is shown below and awaits a mathematical read-back.
-- source:
--   https://github.com/wkshum/ProbabilityTheory/blob/e6387d4fd8005d627d2aec40d10f039ddb4e4b40/ProbabilityTheory/chapter_01/thm_1_2.lean

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_2_F009
import Mathlib.Tactic

open scoped BigOperators Pointwise

open Finset Set

noncomputable section Thm_1_2

namespace DarbouxRS

end DarbouxRS

end Thm_1_2

noncomputable section Darboux_fundamental_result

namespace Refinement

end Refinement

theorem lowerSum_le_of_refinement {a b : ℝ} {f α : ℝ → ℝ}
    (hs : SourceHypotheses a b f α)
    {P P' : Partition a b}
    (R : Refinement P P') :
    lowerSum P f α ≤ lowerSum P' f α := by sorry

namespace Partition

end Partition

end Darboux_fundamental_result
