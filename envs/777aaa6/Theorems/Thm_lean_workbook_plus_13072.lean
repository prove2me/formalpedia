-- Prove2me | Theorems.Thm_lean_workbook_plus_13072
-- name    : lean_workbook_plus_13072
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/33d6b9c0-10ea-4ed2-84bc-03b109aade2a
-- statement:
--   Then, there are $\binom{9}{3}$ ways to choose the three sleepers and the probability is $\dfrac{7+18+30}{\binom{9}{3}} = \frac{55}{84}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13072 (choose 9 3 * (7 + 18 + 30)) / (choose 9 3 * 50) = 55 / 84   :=  by sorry
