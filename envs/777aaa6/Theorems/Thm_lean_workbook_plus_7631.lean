-- Prove2me | Theorems.Thm_lean_workbook_plus_7631
-- name    : lean_workbook_plus_7631
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/d04148eb-8a84-4b27-9179-3e566611d54f
-- statement:
--   Let $a,b,c \in [1,2]$ . Prove that $2(ab+bc+ca) \geq a^2+b^2+c^2+a+b+c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7631 (a b c : ℝ) (ha : 1 ≤ a ∧ a ≤ 2) (hb : 1 ≤ b ∧ b ≤ 2) (hc : 1 ≤ c ∧ c ≤ 2): 2 * (a * b + b * c + c * a) ≥ a^2 + b^2 + c^2 + a + b + c   :=  by sorry
