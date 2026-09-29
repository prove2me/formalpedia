-- Prove2me | Theorems.Thm_lean_workbook_plus_73751
-- name    : lean_workbook_plus_73751
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/38f6312b-d045-4543-9ae6-7f428badd812
-- statement:
--   So we have $1\cdot {9\choose 4}\geq 5 \cdot k$ , and so $k\leq 25$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73751 : 1 * (Nat.choose 9 4) ≥ 5 * k → k ≤ 25   :=  by sorry
