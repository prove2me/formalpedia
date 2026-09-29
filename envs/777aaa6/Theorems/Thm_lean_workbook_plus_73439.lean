-- Prove2me | Theorems.Thm_lean_workbook_plus_73439
-- name    : lean_workbook_plus_73439
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/ca5627e8-e398-4276-be67-30b6bfa132ff
-- statement:
--   For any integer $n$ , we have $15+20n\equiv 15\pmod{20}$ .\n\nIt is because $20n$ is divisible by $20$ no matter what $n$ is.\n\nThis is true even if $n$ is a negative integer; for example, if $n=-1$ , then $15+20n=-5\equiv 15\pmod{20}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73439  (n : ℤ) :
  (15 + 20 * n) % 20 = 15   :=  by sorry
