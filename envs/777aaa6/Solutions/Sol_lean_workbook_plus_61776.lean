-- Prove2me | solution 1 for lean_workbook_plus_61776
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T22:47:08.527246+00:00
-- url     : https://prove2.me/submissions/538902ae-3ca6-49d1-a823-12f49ef9624a

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
theorem solution : ¬ (∀ (f : ℕ → ℕ) (i : f 0 = 0) (ii : f 1 = 1), ∀ n m : ℕ, f (m + n) = f m * f n) := by
  intro h
  have hc := h (fun x : ℕ => x) rfl rfl 1 1
  clear h
  norm_num at hc
