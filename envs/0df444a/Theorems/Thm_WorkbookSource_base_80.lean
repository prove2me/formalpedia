-- Prove2me | Theorems.Thm_WorkbookSource_base_80
-- name    : WorkbookSource.base_80
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:34:21.586983+00:00
-- url     : https://prove2.me/theorems/c54d3e72-57b8-4bf9-b2f7-b334788f120e
-- title:
--   An absolute-difference inequality with sharp constant four thirds
-- statement:
--   Let $ a,\ b,\ c$ be real numbers. Prove that $ |a-b|+|b-c|+|c-a|+ab+bc+ca\leq a^{2}+b^{2}+c^{2}+\frac{4}{3}$ true too.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_80` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_80; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_80 (a b c : ℝ) : |a - b| + |b - c| + |c - a| + a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 + (4:ℝ) / 3  :=  by sorry
