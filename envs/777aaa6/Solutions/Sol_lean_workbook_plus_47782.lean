-- Prove2me | solution 1 for lean_workbook_plus_47782
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T21:04:19.815428+00:00
-- url     : https://prove2.me/submissions/2a30aec2-3219-4cfd-9750-6c3986e4e378

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
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∃ k : ℤ, ¬ (∃ a b c : ℤ, a * b + b * c + c * a = a + b + c + k)) := by
  rintro ⟨k, hk⟩
  apply hk
  refine ⟨0, 0, -k, ?_⟩
  ring
