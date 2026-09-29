-- Prove2me | Theorems.Thm_lean_workbook_plus_41584
-- name    : lean_workbook_plus_41584
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/3a22f5a1-05c4-467a-9080-8d65091b0c25
-- statement:
--   Let $a$ and $b$ be integers. Show that $29$ divides $3a+2b$ if and only if it divides $11a+17b$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41584 : 29 ∣ (3 * a + 2 * b) ↔ 29 ∣ (11 * a + 17 * b)   :=  by sorry
