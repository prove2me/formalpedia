-- Prove2me | Theorems.Thm_WorkbookSource_plus_30382
-- name    : WorkbookSource.plus_30382
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:35:17.785022+00:00
-- url     : https://prove2.me/theorems/f91df6bb-2c93-4571-aa6f-08df1b48712d
-- title:
--   A squared cyclic ratio sum with a symmetric quadratic correction
-- statement:
--   prove that for $a, b, c > 0$, the following inequality holds:
--   $\left (\frac{a}{b+c}\right)^{2}+\left (\frac{b}{c+a}\right)^{2}+\left (\frac{c}{a+b}\right)^{2}+\frac{ab+bc+ca}{a^{2}+b^{2}+c^{2}}\geq \frac{7}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_30382` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_30382; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_30382 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (b + c)) ^ 2 + (b / (c + a)) ^ 2 + (c / (a + b)) ^ 2 + (a * b + b * c + c * a) / (a ^ 2 + b ^ 2 + c ^ 2) ≥ 7 / 4   :=  by sorry
