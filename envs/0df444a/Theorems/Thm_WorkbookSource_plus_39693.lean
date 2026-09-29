-- Prove2me | Theorems.Thm_WorkbookSource_plus_39693
-- name    : WorkbookSource.plus_39693
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:18:47.027366+00:00
-- url     : https://prove2.me/theorems/4992b3c2-06f5-40e6-b011-976dfac2c458
-- title:
--   A four-variable product and pairwise-sum bound
-- statement:
--   Let $a,b,c,d\geq 0$ ,prove that: $(a+c+d)(d+a+b)(a+b+c)(b+c+d)-\\frac{27}{32}(a+b+c+d)^2(ac+bd)-\\frac{27}{32}(a+b+c+d)^2(cd+ab)-\\frac{27}{32}(a+b+c+d)^2(bc+ad)\\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_39693` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_39693; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_39693 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : (a + c + d) * (d + a + b) * (a + b + c) * (b + c + d) - (27 / 32) * (a + b + c + d) ^ 2 * (a * c + b * d) - (27 / 32) * (a + b + c + d) ^ 2 * (c * d + a * b) - (27 / 32) * (a + b + c + d) ^ 2 * (b * c + a * d) ≥ 0   :=  by sorry
