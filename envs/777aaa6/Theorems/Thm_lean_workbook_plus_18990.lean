-- Prove2me | Theorems.Thm_lean_workbook_plus_18990
-- name    : lean_workbook_plus_18990
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/63efb15e-7c23-4880-bbde-4d2745c8d21c
-- statement:
--   If $c \geq b \geq a \geq 0$ . Prove that: $(a+3b)(b+4c)(c+2a) \geq 60abc$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18990 (a b c : ℝ) (hc : c ≥ b ∧ b ≥ a ∧ a ≥ 0) :
  (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c   :=  by sorry
