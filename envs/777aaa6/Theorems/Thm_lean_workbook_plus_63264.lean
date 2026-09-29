-- Prove2me | Theorems.Thm_lean_workbook_plus_63264
-- name    : lean_workbook_plus_63264
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/b7112cbe-b49f-4c31-9ebb-f8b7450da9ab
-- statement:
--   Show that $ \cot \frac{\pi m}{n}\sin \frac{2\pi km}{n} = \frac{\sin \frac{\pi (2k+1)m}{n}}{2\sin \frac{\pi m}{n}} + \frac{\sin \frac{\pi (2k-1)m}{n}}{2\sin \frac{\pi m}{n}} =1+\sum_{j=1}^k \cos \frac{2\pi j m}{n} + \sum_{j=1}^{k-1} \cos \frac{2\pi j m}{n}=1-\cos \frac{2\pi k m}{n}+2\sum_{j=1}^k \cos \frac{2\pi j m}{n}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63264 (m n : ℕ) (k : ℤ) : (1 / Real.tan (π * m / n)) * Real.sin (2 * π * k * m / n) = (Real.sin (π * (2 * k + 1) * m / n) / (2 * Real.sin (π * m / n))) + (Real.sin (π * (2 * k - 1) * m / n) / (2 * Real.sin (π * m / n)))   :=  by sorry
