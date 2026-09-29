-- Prove2me | solution 1 for lean_workbook_plus_48648
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T00:43:25.294121+00:00
-- url     : https://prove2.me/submissions/6ad6f9dd-21ad-4579-b3df-f48ce514c817

import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (n a k : ℝ) (h₁ : n = a + k) (h₂ : a = ⌊n⌋) (h₃ : 0 < k) (h₄ : k < 1) : ⌊n⌋ + 1 = ⌈n⌉ := by
  symm
  apply Int.ceil_eq_iff.mpr
  push_cast
  constructor <;> linarith
