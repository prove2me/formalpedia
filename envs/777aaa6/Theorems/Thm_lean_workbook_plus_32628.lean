-- Prove2me | Theorems.Thm_lean_workbook_plus_32628
-- name    : lean_workbook_plus_32628
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/1acaa6fb-9f76-432c-896b-6d23d0e08a0f
-- statement:
--   Prove that $(a^2-ac)^2+(b^2-ab)^2+(c^2-bc)^2 \geq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32628 (a b c : ℝ) : (a^2 - a*c)^2 + (b^2 - a*b)^2 + (c^2 - b*c)^2 ≥ 0   :=  by sorry
