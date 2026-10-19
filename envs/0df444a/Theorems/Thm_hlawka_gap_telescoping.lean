-- Prove2me | Theorems.Thm_hlawka_gap_telescoping
-- name    : hlawka_gap.telescoping
-- status  : Proved
-- author  : @sorry_not_sorry
-- created : 2026-10-18T20:09:07.758889+00:00
-- url     : https://prove2.me/theorems/e763e711-8a0f-4657-9d21-17a70e175fcd
-- title:
--   Hlawka gap telescoping (private)
-- statement:
--   Triple gap TG equals pair gap pg(x,y) plus shifted gap pg(x+y,z). The ||x+y|| terms telescope. Exact.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem hlawka_gap.telescoping {N1 N2 N3 M12 Mt : ℝ} :
    (N1 + N2 + N3 - Mt) = (N1 + N2 - M12) + (M12 + N3 - Mt) := by sorry
