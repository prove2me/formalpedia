-- Prove2me | Theorems.Thm_WorkbookSource_base_13753
-- name    : WorkbookSource.base_13753
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:44:56.58432+00:00
-- url     : https://prove2.me/theorems/3f53b378-1393-4035-a183-faf5c7b0b750
-- title:
--   A fifth-degree bound involving triangle factors
-- statement:
--   Let $a,b,c $ are postive real numbers, show that:
--
--    $ (a^{2}+b^{2}+c^{2})(a+b-c)(b+c-a)(c+a-b)\leq abc(ab+bc+ac) $
--
--    have fun!
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13753` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13753; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_13753 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) * (a + b - c) * (b + c - a) * (c + a - b) ≤ a * b * c * (a * b + b * c + a * c)  :=  by sorry
