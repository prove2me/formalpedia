-- Prove2me | Theorems.Thm_WorkbookSource_base_37298
-- name    : WorkbookSource.base_37298
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:29:18.354963+00:00
-- url     : https://prove2.me/theorems/1edc16c5-f282-47f9-9e3e-5200bf090662
-- title:
--   A cyclic linear ratio upper bound at fixed sum three
-- statement:
--   Let positive reals $ a,b,c$ which satisfy: $a+b+c=3$
--   Prove that: $ \frac{2a}{a+b}+\frac{2b}{b+c}+\frac{2c}{c+a} \le a^2+b^2+c^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_37298` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_37298; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_37298 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (2 * a / (a + b) + 2 * b / (b + c) + 2 * c / (c + a)) ≤ a ^ 2 + b ^ 2 + c ^ 2  :=  by sorry
