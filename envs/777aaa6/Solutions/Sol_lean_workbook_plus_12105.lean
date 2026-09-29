-- Prove2me | solution 1 for lean_workbook_plus_12105
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:49:59.95681+00:00
-- url     : https://prove2.me/submissions/9d2fcddf-f371-42fe-959c-62fa23bfb93a

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution : ∀ k : ℤ, (4 * k + 1) ^ 4 - 1 ≡ 0 [ZMOD 16] := by
  intro k
  rw [Int.modEq_iff_dvd]
  refine ⟨-(16*k^4+16*k^3+6*k^2+k),?_⟩
  ring
