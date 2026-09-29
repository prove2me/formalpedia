-- Prove2me | Theorems.Thm_lean_workbook_plus_18043
-- name    : lean_workbook_plus_18043
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/531694e9-7991-4370-828e-51ffe2ad2168
-- statement:
--   My friend made a wonderful manipulation of this inequality into this form: $ (a^2-c^2-2ab+bc+ac)^2+(b^2-a^2-2bc+ab+ac)^2+(c^2-b^2-2ac+ab+bc)^2\ge0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18043 (a b c : ℝ) : (a^2 - c^2 - 2 * a * b + b * c + a * c)^2 + (b^2 - a^2 - 2 * b * c + a * b + a * c)^2 + (c^2 - b^2 - 2 * a * c + a * b + b * c)^2 ≥ 0   :=  by sorry
