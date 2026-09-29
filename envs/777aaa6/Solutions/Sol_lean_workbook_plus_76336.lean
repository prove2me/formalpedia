-- Prove2me | solution 1 for lean_workbook_plus_76336
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:16:46.620849+00:00
-- url     : https://prove2.me/submissions/6a3374ee-2bbc-4991-8fdc-f83f5a039079

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℝ) (hab : a ≤ b) (s : Set ℝ) (hs : a ≤ b ∧ b ≤ a) : IsClosed s → s ⊆ Set.Icc a b → IsCompact s := by
  clear hs hab
  intro hclosed hsub
  exact isCompact_Icc.of_isClosed_subset hclosed hsub
