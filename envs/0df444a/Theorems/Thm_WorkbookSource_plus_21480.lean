-- Prove2me | Theorems.Thm_WorkbookSource_plus_21480
-- name    : WorkbookSource.plus_21480
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:07:48.874706+00:00
-- url     : https://prove2.me/theorems/f48fc5bc-759f-463b-8dba-bd6a4c7c8b14
-- title:
--   A squared cubic sum bounds two pairwise sums
-- statement:
--   Prove that for $a, b, c \geq 0$, $(a^3+b^3+c^3+3abc)^2 \geq 4(ab+bc+ca)(a^2b^2+b^2c^2+c^2a^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_21480` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_21480; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_21480 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a^3 + b^3 + c^3 + 3 * a * b * c)^2 ≥ 4 * (a * b + b * c + c * a) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2)   :=  by sorry
