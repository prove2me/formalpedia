-- Prove2me | Theorems.Thm_lean_workbook_plus_2275
-- name    : lean_workbook_plus_2275
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/68ff638e-d03f-4cd0-9643-ef346db81dcd
-- statement:
--   In our case, $u=\frac{\pi}{36}$ and the three roots are $\boxed{\left\{\tan \frac{\pi}{36},\tan \frac{13\pi}{36},\tan \frac{25\pi}{36}\right\}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2275 :
  (Real.tan (π / 36)) ∈ ({tan (π / 36), tan (13 * π / 36), tan (25 * π / 36)} : Set ℝ)   :=  by sorry
