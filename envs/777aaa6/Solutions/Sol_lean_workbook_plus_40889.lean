-- Prove2me | solution 1 for lean_workbook_plus_40889
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:13:18.954946+00:00
-- url     : https://prove2.me/submissions/926f0b52-448c-4bf0-8ecc-e55d74c83fec

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) : x - 1 ≤ ⌊x⌋ ∧ ⌊x⌋ ≤ x := by
  exact ⟨(Int.sub_one_lt_floor x).le,Int.floor_le x⟩
