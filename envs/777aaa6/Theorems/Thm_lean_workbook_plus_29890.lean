-- Prove2me | Theorems.Thm_lean_workbook_plus_29890
-- name    : lean_workbook_plus_29890
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/294e3607-2f32-4f89-ba0b-c64402147ac1
-- statement:
--   prove that $ (a + 3b)(b + 4c)(c + 2a)\ge 60abc$, where $(c\ge b\ge a\ge 0)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29890 (a b c : ℝ) (h : c ≥ b ∧ b ≥ a ∧ a ≥ 0) :
  (a + 3 * b) * (b + 4 * c) * (c + 2 * a) ≥ 60 * a * b * c   :=  by sorry
