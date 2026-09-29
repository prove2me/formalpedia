-- Prove2me | solution 1 for lean_workbook_plus_62734
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T21:11:10.866602+00:00
-- url     : https://prove2.me/submissions/67e2e6a7-5c27-4e6d-96a8-585e48fbd8af

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (x y z : ℝ) :
  |x| + |y| + |z| + |x + y + z| ≥ |x + y| + |y + z| + |z + x| := by
  rcases abs_cases (x + y) with ⟨hxy, _⟩ | ⟨hxy, _⟩ <;>
    rcases abs_cases (y + z) with ⟨hyz, _⟩ | ⟨hyz, _⟩ <;>
    rcases abs_cases (z + x) with ⟨hzx, _⟩ | ⟨hzx, _⟩ <;>
    linarith only [hxy, hyz, hzx, le_abs_self x, neg_le_abs x, le_abs_self y, neg_le_abs y, le_abs_self z, neg_le_abs z, le_abs_self (x + y + z), neg_le_abs (x + y + z)]
