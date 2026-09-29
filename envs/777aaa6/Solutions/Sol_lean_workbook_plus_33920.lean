-- Prove2me | solution 1 for lean_workbook_plus_33920
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:51:57.656246+00:00
-- url     : https://prove2.me/submissions/dbbac15e-d304-4ecb-8189-bd8eee37e64e

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (S : Set ℝ) (hS : S.Nonempty) (hS' : ∃ x, ∀ y ∈ S, y ≤ x) : ∃ x, IsLUB S x := by
  exact ⟨sSup S, isLUB_csSup hS hS'⟩
