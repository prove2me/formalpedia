-- Prove2me | Theorems.Thm_lean_workbook_plus_26548
-- name    : lean_workbook_plus_26548
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/69d57df0-8259-4ab5-9389-84a16bb4c572
-- statement:
--   Show that, $ln\left ( n+1 \right )<n$ , for all $n\geq 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26548 (n : ℕ) (hn : 1 ≤ n) : Real.log (n + 1) < n   :=  by sorry
