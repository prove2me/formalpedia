-- Prove2me | solution 1 for lean_workbook_plus_31325
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T16:57:23.891714+00:00
-- url     : https://prove2.me/submissions/ea9f358c-dca8-4a91-864a-5faa464cfbfb

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ a b c : ℝ, a^5 + b^5 + c^5 + a * b * c * (a^2 + b^2 + c^2) ≥ a^4 * b + a * b^4 + b^4 * c + b * c^4 + c^4 * a + c * a^4) := by
  push_neg
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ 0 , ?_⟩
  norm_num at *
  refine ⟨ -  1 , ?_⟩
  norm_num at *
