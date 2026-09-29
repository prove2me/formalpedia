-- Prove2me | Theorems.Thm_lean_workbook_plus_11448
-- name    : lean_workbook_plus_11448
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/3d5a71a4-8aad-4208-86e9-c866c09e7b54
-- statement:
--   $ 7n+1~|~7n+1 \Rightarrow 7n+1~|~8(7n+1) \Leftrightarrow 7n+1~|~56n+8.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11448 : 7 * n + 1 ∣ 7 * n + 1 → 7 * n + 1 ∣ 8 * (7 * n + 1) ↔ 7 * n + 1 ∣ 56 * n + 8   :=  by sorry
