-- Prove2me | solution 1 for lean_workbook_plus_30327
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:56:19.76272+00:00
-- url     : https://prove2.me/submissions/c6afe422-5fd4-46f2-876a-f10e4a71e8bb

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
theorem solution : ¬ (∀ (a : ℕ → ℝ) (a0 : a 0 = 2) (a_rec : ∀ n, a (n + 1) = 2 + a n / 2), ∀ n, a n < 3) := by
  intro h
  let a : ℕ → ℝ := Nat.rec 2 (fun _ q => 2 + q / 2)
  have hc := h a rfl (by intro n; rfl) 1
  change (2 : ℝ) + 2 / 2 < 3 at hc
  norm_num at hc <;> grind
