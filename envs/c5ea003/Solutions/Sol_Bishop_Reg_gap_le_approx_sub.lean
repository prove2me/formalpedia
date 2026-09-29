-- Prove2me | solution 1 for Bishop.Reg.gap_le_approx_sub
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T15:24:30.286388+00:00
-- url     : https://prove2.me/submissions/5b287a07-b890-4bf7-8baf-cbfddbc399ca

import Mathlib
import Definitions.Def_Logic_ConstructiveAnalysis_BishopReals
import Definitions.Def_Logic_ConstructiveAnalysis_ComputableReals
import Definitions.Def_Logic_ConstructiveAnalysis_ConstructiveOrder
open Bishop Bishop.Reg in
theorem solution (x y : Reg) (n : ℕ) {m : ℕ}
    (hm : 1 / (m + 1 : ℚ) ≤ gapAt x y n / 8) :
    3 * gapAt x y n / 4 ≤ y.approx m - x.approx m := by
  -- regularity: moving from index `n` to `m` costs at most `1/(m+1) + 1/(n+1)` per sequence
  have hy := abs_le.mp (y.regular m n)
  have hx := abs_le.mp (x.regular m n)
  unfold gapAt at hm ⊢
  have e : (2 : ℚ) / (n + 1) = 2 * (1 / (n + 1)) := by ring
  rw [e] at hm ⊢
  linarith [hy.1, hy.2, hx.1, hx.2]
