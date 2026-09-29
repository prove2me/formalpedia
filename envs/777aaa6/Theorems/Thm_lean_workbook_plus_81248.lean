-- Prove2me | Theorems.Thm_lean_workbook_plus_81248
-- name    : lean_workbook_plus_81248
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/7c92a4b7-5b71-4e67-aa08-96bc371900f1
-- statement:
--   $ 7n+1 ~|~ 8n+55 \Rightarrow 7n+1~|~7(8n+55) \Leftrightarrow 7n+1~|~56n+385.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81248 (n : ℕ) : 7 * n + 1 ∣ 8 * n + 55 → 7 * n + 1 ∣ 56 * n + 385   :=  by sorry
