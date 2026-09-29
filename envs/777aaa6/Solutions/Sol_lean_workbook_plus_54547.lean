-- Prove2me | solution 1 for lean_workbook_plus_54547
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:39:44.333683+00:00
-- url     : https://prove2.me/submissions/10168987-3d32-4290-8e0b-319d51c72ea8

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∃ a : ℕ → ℤ, a 0 = 2 ∧ ∀ n, a (n + 1) = 2 * a n - 1 := by
  refine ⟨fun n => (2 : ℤ)^n+1,by norm_num,?_⟩
  intro n
  ring
