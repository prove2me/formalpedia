-- Prove2me | solution 1 for lean_workbook_plus_48859
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:37:46.707446+00:00
-- url     : https://prove2.me/submissions/1e01ff36-b461-4e84-af74-afeddb7e4547

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (x : ℕ → ℕ) (hx : x 1 = 21 ∧ x 2 = 17 ∧ x 3 = 16 ∧ x 4 = 14), 4 * (x 1 / x 2 + x 2 / x 3 + x 3 / x 4 + x 4 / x 1) - (x 1 + x 2 + x 3 + x 4) * (1 / x 1 + 1 / x 2 + 1 / x 3 + 1 / x 4) = 10 / 119) := by
  intro h
  let x : ℕ → ℕ := fun n => if n=1 then 21 else if n=2 then 17 else if n=3 then 16 else 14
  have hc := h x (by norm_num [x])
  norm_num [x] at hc <;> grind
