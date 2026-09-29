-- Prove2me | Theorems.Thm_lean_workbook_plus_9989
-- name    : lean_workbook_plus_9989
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/830e55d9-7e60-43dc-8c41-79486f216d73
-- statement:
--   $5(a^{2}+b^{2}+c^{2})(a+b+c)\leq 6(a^{3}+b^{3}+c^{3})+(a+b+c)^3 \Longleftrightarrow a^3+b^3+c^3+3abc \geq \sum_{cyc} (a^2b+b^2a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9989 (a b c : ℝ) :
  5 * (a ^ 2 + b ^ 2 + c ^ 2) * (a + b + c) ≤ 6 * (a ^ 3 + b ^ 3 + c ^ 3) + (a + b + c) ^ 3 ↔
    a ^ 3 + b ^ 3 + c ^ 3 + 3 * a * b * c ≥ a ^ 2 * b + b ^ 2 * a + a ^ 2 * c + c ^ 2 * a + b ^ 2 * c + c ^ 2 * b   :=  by sorry
