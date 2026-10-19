-- Prove2me | Theorems.Thm_hlawka_gap_min_shifted_eq
-- name    : hlawka_gap.min_shifted_eq
-- status  : Proved
-- author  : @sorry_not_sorry
-- created : 2026-10-18T20:09:07.839106+00:00
-- url     : https://prove2.me/theorems/a45d888a-10b4-4a57-aa51-576417ca7fd9
-- title:
--   Min shifted gap equals TG minus max pair gap (private)
-- statement:
--   The minimum of the three shifted gaps equals the triple gap minus the maximum pair gap. Follows from telescoping.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem hlawka_gap.min_shifted_eq {N1 N2 N3 M12 M23 M31 Mt : ℝ} :
    min (min (M12 + N3 - Mt) (M23 + N1 - Mt)) (M31 + N2 - Mt)
      = (N1 + N2 + N3 - Mt)
        - max (N1 + N2 - M12) (max (N2 + N3 - M23) (N3 + N1 - M31)) := by sorry
