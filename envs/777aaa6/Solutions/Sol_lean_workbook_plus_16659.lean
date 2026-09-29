-- Prove2me | solution 1 for lean_workbook_plus_16659
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:56:00.310625+00:00
-- url     : https://prove2.me/submissions/40cf97f5-f550-43b4-9cb4-89927efdcaef

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b : ℤ) : a^2 + b^2 ≡ (a + b)^2 [ZMOD a * b] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨2,?_⟩
  ring
