-- Prove2me | Theorems.Thm_lean_workbook_plus_68580
-- name    : lean_workbook_plus_68580
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/33405e8e-7b80-4271-bb3d-48903008ca87
-- statement:
--   Prove that $ 2F_{n+2}^2 + 2F_{n+1}^2 - F_{n}^2 = F_{n+3}^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68580 (n : ℕ) : 2 * fib (n + 2) ^ 2 + 2 * fib (n + 1) ^ 2 - fib n ^ 2 = fib (n + 3) ^ 2   :=  by sorry
