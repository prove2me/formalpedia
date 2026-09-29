-- Prove2me | Theorems.Thm_lean_workbook_plus_59282
-- name    : lean_workbook_plus_59282
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/3018a949-6306-48ad-94d6-92f9392f49bf
-- statement:
--   Show that $a^{2}+b^{2}+c^{2}-ab-ac-bc \geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59282 (a b c : ℝ) : a ^ 2 + b ^ 2 + c ^ 2 - (a * b + a * c + b * c) ≥ 0   :=  by sorry
