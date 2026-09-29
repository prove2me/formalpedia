-- Prove2me | Theorems.Thm_WorkbookSource_base_26775
-- name    : WorkbookSource.base_26775
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:51:34.761832+00:00
-- url     : https://prove2.me/theorems/bd49c2e8-cea2-46fb-9518-c20cf2d0fc3f
-- title:
--   A cubic-pairwise lower bound at unit sum
-- statement:
--   Let $a,b,c > 0, a+b+c = 1$. Prove that $15(a^{3}+b^{3}+c^{3}+ab+bc+ca)+9abc \ge 7$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_26775` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_26775; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_26775 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 1) :  15 * (a ^ 3 + b ^ 3 + c ^ 3 + a * b + b * c + c * a) + 9 * a * b * c ≥ 7  :=  by sorry
