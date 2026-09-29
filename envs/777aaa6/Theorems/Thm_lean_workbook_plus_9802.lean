-- Prove2me | Theorems.Thm_lean_workbook_plus_9802
-- name    : lean_workbook_plus_9802
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/1e0209bc-c754-4f67-8176-ec0ed721360b
-- statement:
--   Prove that $F_n^2 + F_{n + 1}^2 = F_{2n + 1}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9802 (n : ℕ) : fib n ^ 2 + fib (n + 1) ^ 2 = fib (2 * n + 1)   :=  by sorry
