-- Prove2me | Theorems.Thm_lean_workbook_plus_37170
-- name    : lean_workbook_plus_37170
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/a1da79fb-2bbc-4582-832c-b835a9c979e6
-- statement:
--   Prove that $e_n = (1 + \frac{1}{n})^n = 1+ 1 + \frac{1}{2!} (1 - \frac{1}{n}) + \frac{1}{3!}(1 -\frac{1}{n})(1 -\frac{2}{n}) + \cdots + \frac{1}{n!} (1 -\frac{1}{n})(1 - \frac{2}{n}) \cdots (1 -\frac{n-1}{n})$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37170 : ∀ n : ℕ, (1 + 1 / n)^n = ∑ k in Finset.range n, 1 / (k + 1)! * ∏ i in Finset.range k, (1 - i / n)   :=  by sorry
