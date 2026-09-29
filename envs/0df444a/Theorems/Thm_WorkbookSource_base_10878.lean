-- Prove2me | Theorems.Thm_WorkbookSource_base_10878
-- name    : WorkbookSource.base_10878
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:33:02.237991+00:00
-- url     : https://prove2.me/theorems/eb72fc42-93e8-4f02-b3c0-cc6a1e41c4f6
-- title:
--   A cyclic ratio lower bound involving three symmetric products
-- statement:
--   For any positive real numbers $a,\ b$ and $c$ ,
--    $\frac{a}{a+b}+\frac{b}{b+c}+\frac{c}{c+a} \ge \frac{27abc}{2(a+b+c)(ab+bc+ca)}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_10878` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_10878; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_10878 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (a + b) + b / (b + c) + c / (c + a)) ≥ 27 * a * b * c / (2 * (a + b + c) * (a * b + b * c + c * a))  :=  by sorry
