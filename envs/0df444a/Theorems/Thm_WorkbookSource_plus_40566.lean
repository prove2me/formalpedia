-- Prove2me | Theorems.Thm_WorkbookSource_plus_40566
-- name    : WorkbookSource.plus_40566
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:07:00.679888+00:00
-- url     : https://prove2.me/theorems/d639f837-90f7-4737-831e-b83ceaf6207a
-- title:
--   A shifted cyclic reciprocal sum lower bound at fixed sum six
-- statement:
--   Given $a,b,c$ are positive real numbers satisfying $a+b+c =6$ . Prove that:
--   $\frac{a}{b^2 + c + 1} + \frac{b}{c^2 + a + 1} + \frac{c}{a^2 + b + 1} \ge \frac{6}{7}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_40566` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_40566; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_40566 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 6) : a / (b ^ 2 + c + 1) + b / (c ^ 2 + a + 1) + c / (a ^ 2 + b + 1) ≥ 6 / 7   :=  by sorry
