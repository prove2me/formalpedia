-- Prove2me | solution 1 for lean_workbook_plus_10545
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:35:47.268298+00:00
-- url     : https://prove2.me/submissions/4d48538e-7ce9-4919-b159-218a1c40189b

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (f : ℝ → ℝ) (hf: ∀ x, x ≠ 0 → f x / x = f 1 / 1) : ∀ x, x ≠ 0 → f x = f 1 * x := by
  intros
  grind
