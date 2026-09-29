-- Prove2me | Theorems.Thm_lean_workbook_plus_9622
-- name    : lean_workbook_plus_9622
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/17ee6059-7760-4a8a-b41d-01151e5b1260
-- statement:
--   When $a,b,c\geq 0$ $(a+b+c)(ab+bc+ca)\geq 9abc$ !
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9622 {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a + b + c) * (a * b + b * c + c * a) ≥ 9 * a * b * c   :=  by sorry
