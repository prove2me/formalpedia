-- Prove2me | Theorems.Thm_Zeta9Note_min_lt_weighted_average_lt_max
-- name    : Zeta9Note.min_lt_weighted_average_lt_max
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-09-25T07:31:01.880969+00:00
-- url     : https://prove2.me/theorems/0014e3ef-7b09-4288-8256-09c7b53db866
-- title:
--   A non-degenerate weighted average lies strictly between min and max
-- statement:
--   Let w be a strictly positive weight vector on five indices with total weight 1, and let r be a five-tuple that is not constant. Then some entry of r is strictly below the weighted average of r, and some entry is strictly above it.
-- source:
--   Abstract layer distilled from the v0.1 research note (Zenodo 10.5281/zenodo.22951155); statement and proof in formalization/Zeta9Note.lean.

import Mathlib

namespace Zeta9Note

theorem min_lt_weighted_average_lt_max
    (w r : Fin 5 → ℝ) (hw : ∀ j : Fin 5, 0 < w j)
    (hsum : ∑ j : Fin 5, w j = 1)
    (hnd : ∃ j j' : Fin 5, r j ≠ r j') :
    (∃ j : Fin 5, r j < ∑ i : Fin 5, w i * r i) ∧
      (∃ j : Fin 5, (∑ i : Fin 5, w i * r i) < r j) := by sorry

end Zeta9Note
