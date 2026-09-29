-- Prove2me | Theorems.Thm_lean_workbook_plus_47342
-- name    : lean_workbook_plus_47342
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/e8282ebe-fa49-476c-9d8f-4bbb6ce73ca2
-- statement:
--   Let's say you have 5 numbers: $a$ , $b$ , $c$ , $d$ , and $e$ . Prove that if you add 30 to EACH number, you increase their total sum by 150.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47342 (a b c d e : ℕ) : (a + b + c + d + e) + 150 = (a + 30 + b + 30 + c + 30 + d + 30 + e + 30)   :=  by sorry
