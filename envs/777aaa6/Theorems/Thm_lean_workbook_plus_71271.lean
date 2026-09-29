-- Prove2me | Theorems.Thm_lean_workbook_plus_71271
-- name    : lean_workbook_plus_71271
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/0d30ce4a-cb17-4042-9c00-16ba002fbf28
-- statement:
--   Let $a,b,c$ be real. Prove that: $a^2+b^2+c^2+2(ab+bc+ca)\geq0;$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71271 (a b c : ℝ) : a^2 + b^2 + c^2 + 2 * (a * b + b * c + c * a) ≥ 0   :=  by sorry
