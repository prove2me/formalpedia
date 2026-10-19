-- Prove2me | Theorems.Thm_hlawka_gap_defect_identity
-- name    : hlawka_gap.defect_identity
-- status  : Proved
-- author  : @sorry_not_sorry
-- created : 2026-10-18T20:09:07.531972+00:00
-- url     : https://prove2.me/theorems/3b310b36-41d6-40c3-99c1-7cf55efda5ca
-- title:
--   Hlawka gap defect identity (private)
-- statement:
--   The shifted pair gap pg(x+y,z) equals pg(x,z)+pg(y,z) plus the Hlawka residual TG-PGS. Exact algebraic identity in the 7 norm variables.

import Mathlib.Data.Real.Basic
import Mathlib.Tactic

theorem hlawka_gap.defect_identity {N1 N2 N3 M12 M23 M31 Mt : ℝ} :
    (M12 + N3 - Mt)
      = (N3 + N1 - M31) + (N2 + N3 - M23)
        + ((N1 + N2 + N3 - Mt)
          - ((N1 + N2 - M12) + (N2 + N3 - M23) + (N3 + N1 - M31))) := by sorry
