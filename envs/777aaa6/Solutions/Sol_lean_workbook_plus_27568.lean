-- Prove2me | solution 1 for lean_workbook_plus_27568
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:47:22.797892+00:00
-- url     : https://prove2.me/submissions/ff0c9ddb-4035-4a20-9eed-3ade1ed5873e

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (f g : ℝ → ℝ) (hf : f = fun x => if x < 0 then -1 else 1) (hg : g = fun _ => 0) : Continuous (g ∘ f) := by
  rw [hg]
  exact continuous_const
