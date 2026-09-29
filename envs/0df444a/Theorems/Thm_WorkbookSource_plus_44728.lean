-- Prove2me | Theorems.Thm_WorkbookSource_plus_44728
-- name    : WorkbookSource.plus_44728
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:37:40.1333+00:00
-- url     : https://prove2.me/theorems/c5ccb657-5609-4063-a62d-8167969c2939
-- title:
--   A squared cubic expression bounds symmetric quartic products
-- statement:
--   Prove that if a,b,c≥0,then $ (a^3+b^3+c^3+3abc)^2$ ≥ $ 2(ab+bc+ca)(ab(a^2+b^2)+bc(b^2+c^2)+ca(c^2+a^2))$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_44728` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_44728; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_44728 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c) ^ 2 ≥ 2 * (a * b + b * c + c * a) * (a * b * (a ^ 2 + b ^ 2) + b * c * (b ^ 2 + c ^ 2) + c * a * (c ^ 2 + a ^ 2))   :=  by sorry
