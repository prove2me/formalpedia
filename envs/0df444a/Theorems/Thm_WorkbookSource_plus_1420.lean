-- Prove2me | Theorems.Thm_WorkbookSource_plus_1420
-- name    : WorkbookSource.plus_1420
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:52:14.717793+00:00
-- url     : https://prove2.me/theorems/9b7c33f4-9816-4d07-8c3b-55d0965d6005
-- title:
--   A squared cyclic ratio sum has a symmetric quadratic upper bound
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that:
--    $ \left(\frac{a}{a+b}\right)^2+ \left(\frac{b}{b+c}\right)^2+ \left(\frac{c}{c+a}\right)^2\leq \frac{3(a^2+b^2+c^2)}{4(ab+bc+ca)} $ Similar problems: <https://artofproblemsolving.com/community/q1h1814384p12099563>
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_1420` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_1420; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_1420 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (a + b)) ^ 2 + (b / (b + c)) ^ 2 + (c / (c + a)) ^ 2 ≤ (3 * (a ^ 2 + b ^ 2 + c ^ 2)) / (4 * (a * b + b * c + a * c))   :=  by sorry
