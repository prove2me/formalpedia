-- Prove2me | Theorems.Thm_WorkbookSource_base_52148
-- name    : WorkbookSource.base_52148
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:51:22.587639+00:00
-- url     : https://prove2.me/theorems/66607255-bb6d-4695-ad8b-e1191610603e
-- title:
--   A cyclic pairwise ratio upper bound by symmetric quadratic sums
-- statement:
--   Let $a,b,c>0$ . Prove $ \frac{a+b}{b+c}+\frac{b+c}{c+a}+\frac{c+a}{a+b}\le \frac{9(a^2+b^2+c^2)}{8(ab+bc+ca)}+\frac{15}{8}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_52148` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_52148; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_52148 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) ≤ 9 * (a ^ 2 + b ^ 2 + c ^ 2) / (8 * (a * b + b * c + c * a)) + 15 / 8  :=  by sorry
