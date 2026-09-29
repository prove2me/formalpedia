-- Prove2me | solution 1 for lean_workbook_plus_70394
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T04:22:13.640112+00:00
-- url     : https://prove2.me/submissions/77520054-9eba-4079-9a13-4fc60fcfd199

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr
set_option autoImplicit false
set_option maxHeartbeats 500000
theorem solution (f : ℤ → ℤ) (hf: f = fun x ↦ x) : ∀ x y, f (x + y) * f (f x - y) = x * f x - y * f y   :=  by
  subst f
  intro x y
  ring
#print axioms solution
