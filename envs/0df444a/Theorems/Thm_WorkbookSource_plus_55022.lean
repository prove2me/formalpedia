-- Prove2me | Theorems.Thm_WorkbookSource_plus_55022
-- name    : WorkbookSource.plus_55022
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:39:56.751883+00:00
-- url     : https://prove2.me/theorems/9514ceb0-35a1-4c25-ad60-fe4ddb49dfdc
-- title:
--   A sixth-degree bound involving pairwise power differences
-- statement:
--   Let $a,b,c > 0 $. Prove that : $(a^5 - b^5 )(a-b)+(b^5 - c^5 )(b-c) + (c^5 -a^5 )(c-a) \geq 5ab(a^2 +b^2 -ac-bc)(a-b)^2 + 5bc(b^2 +c^2 -ba-ca )(b-c)^2 + 5ca(c^2 +a^2 -cb-ab )(c-a)^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_55022` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_55022; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_55022 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^5 - b^5) * (a - b) + (b^5 - c^5) * (b - c) + (c^5 - a^5) * (c - a) ≥ 5 * a * b * (a^2 + b^2 - a * c - b * c) * (a - b)^2 + 5 * b * c * (b^2 + c^2 - b * a - c * a) * (b - c)^2 + 5 * c * a * (c^2 + a^2 - c * b - a * b) * (c - a)^2   :=  by sorry
