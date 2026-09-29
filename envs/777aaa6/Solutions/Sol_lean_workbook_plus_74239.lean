-- Prove2me | solution 1 for lean_workbook_plus_74239
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T23:15:04.00051+00:00
-- url     : https://prove2.me/submissions/7499a5fc-9f17-4dac-bcfd-355820395996

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
theorem solution : ¬ (∀ (n : ℕ) (f : ℕ → ℕ) (hf: f 1 = 2 ∧ ∀ n, f (n + 1) = 10 * f n + 2 * n + 2), f n = 12 * 10 ^ (n - 1) + 2 * n - 10) := by
  let f : ℕ → ℕ := Nat.rec 0 (fun n r => 10*r+2*n+2)
  have h1 : f 1=2 := by rfl
  have hr : ∀ n, f (n+1)=10*f n+2*n+2 := by intro n; rfl
  have h2 : f 2=24 := by rfl
  intro h
  have hc := h 2 f ⟨h1,hr⟩
  rw [h2] at hc
  norm_num at hc
