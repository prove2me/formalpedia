-- Prove2me | solution 1 for lean_workbook_plus_21514
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:43:23.177693+00:00
-- url     : https://prove2.me/submissions/1c44584c-11ec-4366-9166-7cbdd1895465

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : ∀ a b : ℝ, (a - b * Complex.I) / (a ^ 2 + b ^ 2) = (a + b * Complex.I)⁻¹ := by
  intro a b
  rw [Complex.inv_def, Complex.normSq_add_mul_I]
  simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring
