-- Prove2me | solution 1 for lean_workbook_plus_34483
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:50:55.504637+00:00
-- url     : https://prove2.me/submissions/483a769a-f86c-4ae9-81f4-200ab6b1b9af

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (f g : ℝ → ℝ) (hf : ∀ x, f x = if x < 0 then -1 else 1) (hg : ∀ x, g x = 0) : Continuous (g ∘ f) := by
  have he : g ∘ f = fun _ => (0:ℝ) := by funext x; exact hg (f x)
  rw [he]
  exact continuous_const
