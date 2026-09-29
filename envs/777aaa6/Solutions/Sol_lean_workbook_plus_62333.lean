-- Prove2me | solution 1 for lean_workbook_plus_62333
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T23:07:35.845979+00:00
-- url     : https://prove2.me/submissions/bf618377-7b17-4de9-9571-4c4689e1e64c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (p : ℕ) : p^2 - 3 * p - 2 ≡ (p - 10)^2 [ZMOD 17] := by
  rw [Int.modEq_iff_dvd]
  refine ⟨6-(p:ℤ), ?_⟩
  ring
