-- Prove2me | Theorems.Thm_lean_workbook_plus_11442
-- name    : lean_workbook_plus_11442
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/3c0642e7-d7cf-4191-b7b1-f37249d156b4
-- statement:
--   Let be $x \in \mathbb{Q}$ , then $x=\frac{a}{b}, a,b \in \mathbb{Z}, b >0$ . But then $b \cdot x \equiv 0 \mod \mathbb{Z}$ , so the order of $x$ is finite (and a divisor of $b$ ).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11442 (x : ℚ) : ∃ a b : ℤ, b > 0 ∧ x = a / b   :=  by sorry
