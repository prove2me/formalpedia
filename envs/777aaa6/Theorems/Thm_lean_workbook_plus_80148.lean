-- Prove2me | Theorems.Thm_lean_workbook_plus_80148
-- name    : lean_workbook_plus_80148
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/9136bc47-51d8-4120-ae22-623979b6c53a
-- statement:
--   prove that $(\cos^4x \sin^6y)^{\frac {1}{5}} + (\cos^6y \sin^4x)^{\frac {1}{5}} \le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80148 (x y : ℝ) : (cos x ^ 4 * sin y ^ 6) ^ (1 / 5) + (cos y ^ 6 * sin x ^ 4) ^ (1 / 5) ≤ 1   :=  by sorry
