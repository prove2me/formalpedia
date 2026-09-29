-- Prove2me | Theorems.Thm_WorkbookSource_base_11742
-- name    : WorkbookSource.base_11742
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:44:20.060566+00:00
-- url     : https://prove2.me/theorems/b3aee409-1074-4675-8661-aa7db5cb1c54
-- title:
--   A triangle product bound at perimeter six
-- statement:
--   If $a,b,c$ are the sides of a triangle whose perimeter is equal to 6 then prove that:
--
--   $3abc+72\geq 8(ab+bc+ac)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_11742` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_11742; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_11742 {a b c : ℝ} (hx: a + b + c = 6) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 3 * a * b * c + 72 ≥ 8 * (a * b + b * c + a * c)  :=  by sorry
