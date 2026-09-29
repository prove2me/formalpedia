-- Prove2me | Theorems.Thm_WorkbookSource_plus_44406
-- name    : WorkbookSource.plus_44406
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:37:26.184633+00:00
-- url     : https://prove2.me/theorems/1dbea8be-80e5-4fde-a299-4953a6ef405b
-- title:
--   A symmetric sixth-degree product comparison
-- statement:
--   For $a,b,c>0$ . Prove that $18\cdot abc\cdot \sum_{cyc} a(a+b)(c+a)\leqq (a+b+c)^3\cdot (a+b)(b+c)(c+a)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_44406` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_44406; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_44406 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 18 * a * b * c * (a * (a + b) * (a + c) + b * (b + a) * (b + c) + c * (c + a) * (c + b)) ≤ (a + b + c) ^ 3 * (a + b) * (b + c) * (c + a)   :=  by sorry
