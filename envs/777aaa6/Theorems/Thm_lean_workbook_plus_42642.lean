-- Prove2me | Theorems.Thm_lean_workbook_plus_42642
-- name    : lean_workbook_plus_42642
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/cf3a1824-722d-4334-8945-90faa3c4f752
-- statement:
--   Let $a,b,c \ge 0$ . Prove that: $a^4+b^4+c^4 \ge abc(a+b+c)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42642 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a^4 + b^4 + c^4 ≥ a * b * c * (a + b + c)   :=  by sorry
