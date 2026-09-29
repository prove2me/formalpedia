-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_exponent_unique_real_base_short_interval
-- name    : ErdosProblems.Erdos269.PaperCompleteR20.exponent_unique_real_base_short_interval
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T19:22:26.781663+00:00
-- url     : https://prove2.me/theorems/a35251e1-21e3-496a-ad85-4f18ade488fd
-- title:
--   Exponent unique real base short interval
-- statement:
--   Let a real base be at least one and a real weight be nonnegative. If the interval [lo,hi) has hi≤base·lo, at most one natural exponent e can place base^e·weight in that interval.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/RealBaseShortInterval.lean#L8-L32
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace ErdosProblems.Erdos269.PaperCompleteR20
end ErdosProblems.Erdos269.PaperCompleteR20

/-! Uniqueness in a real short multiplicative interval, including real bases. -/

open ErdosProblems.Erdos269.PaperCompleteR20

theorem ErdosProblems.Erdos269.PaperCompleteR20.exponent_unique_real_base_short_interval
    {base lo hi weight : ℝ} {a b : ℕ}
    (hbase : 1 ≤ base) (hweight : 0 ≤ weight)
    (hwidth : hi ≤ base * lo)
    (haLo : lo ≤ base ^ a * weight) (haHi : base ^ a * weight < hi)
    (hbLo : lo ≤ base ^ b * weight) (hbHi : base ^ b * weight < hi) :
    a = b := by sorry
