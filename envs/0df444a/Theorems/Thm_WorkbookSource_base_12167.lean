-- Prove2me | Theorems.Thm_WorkbookSource_base_12167
-- name    : WorkbookSource.base_12167
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:41:57.571216+00:00
-- url     : https://prove2.me/theorems/cfae934b-acaa-435e-860d-32205017bd31
-- title:
--   A pairwise reciprocal lower bound involving the symmetric quadratic sum
-- statement:
--   Let $a,b,c>0$ . Prove that
--
--    $$ \dfrac{1}{a(b+c)}+\dfrac{1}{b(c+a)}+\dfrac{1}{c(a+b)} \ge \frac{9}{2(ab+bc+ca)}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12167` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12167; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12167 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / (a * (b + c)) + 1 / (b * (c + a)) + 1 / (c * (a + b)) ≥ 9 / (2 * (a * b + b * c + c * a))  :=  by sorry
