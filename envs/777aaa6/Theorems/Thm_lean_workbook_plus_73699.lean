-- Prove2me | Theorems.Thm_lean_workbook_plus_73699
-- name    : lean_workbook_plus_73699
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/982438de-c220-47b9-862b-dd33f5b287fe
-- statement:
--   For $ ab+bc+ca=3$ the following inequalities holds:\n\n1) $ a^2 + b^2 + c^2 + 3abc\ge 6$ (Vasc's inequality)\n\n2) $ a^2 + b^2 + c^2\ge a + b + c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73699 :  ∀ a b c : ℝ, a * b + b * c + c * a = 3 → a ^ 2 + b ^ 2 + c ^ 2 + 3 * a * b * c ≥ 6   :=  by sorry
