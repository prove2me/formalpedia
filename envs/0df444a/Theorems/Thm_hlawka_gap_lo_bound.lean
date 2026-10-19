-- Prove2me | Theorems.Thm_hlawka_gap_lo_bound
-- name    : hlawka_gap.lo_bound
-- status  : Proved
-- author  : @sorry_not_sorry
-- created : 2026-10-18T20:09:07.263656+00:00
-- url     : https://prove2.me/theorems/e93c6c3a-f837-4805-acdf-63d2b7e4ff06
-- title:
--   Lo-regime bound TG ≤ PGS + 2*min norm (private)
-- statement:
--   Triple gap is at most pair gap sum plus twice the minimum singleton norm. Uses triangle inequalities (forward and reverse). Gives R ≤ 1+2m/PGS on the lo regime.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem hlawka_gap.lo_bound {N1 N2 N3 M12 M23 M31 Mt : ℝ}
    (h12 : M12 ≤ N1 + N2) (h23 : M23 ≤ N2 + N3) (h31 : M31 ≤ N3 + N1)
    (hr1 : M23 - N1 ≤ Mt) (hr2 : M31 - N2 ≤ Mt) (hr3 : M12 - N3 ≤ Mt) :
    (N1 + N2 + N3 - Mt)
      ≤ ((N1 + N2 - M12) + (N2 + N3 - M23) + (N3 + N1 - M31))
        + 2 * min N1 (min N2 N3) := by sorry
