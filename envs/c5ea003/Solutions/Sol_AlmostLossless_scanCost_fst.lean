-- Prove2me | solution 1 for AlmostLossless.scanCost_fst
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T08:08:33.873707+00:00
-- url     : https://prove2.me/submissions/300823e3-3605-4c20-8dd0-89331af29b4c

import Mathlib
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
set_option autoImplicit false
open AlmostLossless

theorem solution {α : Type*} {M : ℕ} (h : α → Fin M) (i : Fin M) (l : List α) :
    (scanCost h i l).1 = l.filter (fun y => decide (h y = i)) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
      by_cases hy : h y = i <;> simp [scanCost, hy, ih]
