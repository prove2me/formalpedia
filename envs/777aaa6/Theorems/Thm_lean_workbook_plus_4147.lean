-- Prove2me | Theorems.Thm_lean_workbook_plus_4147
-- name    : lean_workbook_plus_4147
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/38467a47-a688-45f3-88c1-6a4e14209681
-- statement:
--   Find $a$ and $b$ that satisfy both equations.\n\n\\begin{align*}5a+7=22\\6b+10a=42\\end{align*}
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4147 (a b : ℕ) : (5*a+7=22 ∧ 6*b+10*a=42) ↔ a = 3 ∧ b = 2   :=  by sorry
