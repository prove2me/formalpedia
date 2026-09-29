-- Prove2me | Theorems.Thm_lean_workbook_plus_54238
-- name    : lean_workbook_plus_54238
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/67aadcf8-967a-4ae5-8611-e03e527728db
-- statement:
--   Let $a,b,c \in \mathbb{R}$ such that $a^3b+b^3c+c^3a = \frac23(a^2b^2+b^2c^2+c^2a^2)$ . Prove that $(a^2+b^2+c^2)^2 \geq 4(a^3b+b^3c+c^3a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54238 : a^3 * b + b^3 * c + c^3 * a = 2 / 3 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) → (a^2 + b^2 + c^2)^2 ≥ 4 * (a^3 * b + b^3 * c + c^3 * a)   :=  by sorry
