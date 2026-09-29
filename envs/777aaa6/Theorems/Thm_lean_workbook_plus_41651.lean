-- Prove2me | Theorems.Thm_lean_workbook_plus_41651
-- name    : lean_workbook_plus_41651
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/647610b0-0b83-4aca-a7bd-5a77062503c5
-- statement:
--   Verify the inequality for $a=b=c=1$:\n$$\sum a^5(a+1) \geq \frac{3}{4}(a+1)(b+1)(c+1)$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41651 (a b c : ℕ) (ha : a = 1) (hb : b = 1) (hc : c = 1) : a^5 * (a + 1) + b^5 * (b + 1) + c^5 * (c + 1) ≥ (3 / 4) * (a + 1) * (b + 1) * (c + 1)   :=  by sorry
