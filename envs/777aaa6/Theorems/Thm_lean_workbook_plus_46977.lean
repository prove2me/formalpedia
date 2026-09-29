-- Prove2me | Theorems.Thm_lean_workbook_plus_46977
-- name    : lean_workbook_plus_46977
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/be3ce3b4-1283-4dd7-95ac-c21067b7032e
-- statement:
--   Let $t=sinx+cosx \Rightarrow sinxcosx= \frac{t^2-1}{2} ; |t| \le \sqrt{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46977 (x : ℝ) (t : ℝ) (ht : t = sin x + cos x) : sin x * cos x = (t^2 - 1) / 2 ∧ |t| ≤ Real.sqrt 2   :=  by sorry
