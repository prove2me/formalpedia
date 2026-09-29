-- Prove2me | Theorems.Thm_lean_workbook_plus_65126
-- name    : lean_workbook_plus_65126
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/e5cb0c1a-0d06-454e-9c83-c3f6510faefb
-- statement:
--   Prove that $\frac{1}{3}(t+2)\ge \frac{4}{9}(\frac{2t+1}{t+1})^2 \iff \frac{(t-1)^2(3t+2)}{9(t+1)^2}\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65126 : 1 / 3 * (t + 2) ≥ 4 / 9 * ((2 * t + 1) / (t + 1)) ^ 2 ↔ (t - 1) ^ 2 * (3 * t + 2) / (9 * (t + 1) ^ 2) ≥ 0   :=  by sorry
