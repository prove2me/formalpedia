-- Prove2me | Theorems.Thm_lean_workbook_plus_46600
-- name    : lean_workbook_plus_46600
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/8da09457-cde9-4f70-8315-f0bb70f5c4aa
-- statement:
--   Second equation: \n $ \rightarrow \cos(x-y)-\cos(x+y)=n \rightarrow 2\cos^{2}\frac{x-y}{2}-2\cos^{2}\frac{x+y}{2}=n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46600 (x y n : ℝ) : (cos (x - y) - cos (x + y) = n ↔ 2 * cos ((x - y) / 2) ^ 2 - 2 * cos ((x + y) / 2) ^ 2 = n)   :=  by sorry
