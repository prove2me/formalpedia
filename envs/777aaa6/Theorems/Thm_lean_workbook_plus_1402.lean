-- Prove2me | Theorems.Thm_lean_workbook_plus_1402
-- name    : lean_workbook_plus_1402
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/03d19bf2-d5b6-4e99-a4df-59648237b653
-- statement:
--   Let $a,b,c \in [1,2]$ . Prove that $2(ab+bc+ca) \geq a^2+b^2+c^2+a+b+c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1402 {a b c : ℝ} (ha : 1 ≤ a ∧ a ≤ 2) (hb : 1 ≤ b ∧ b ≤ 2) (hc : 1 ≤ c ∧ c ≤ 2) : 2 * (a * b + b * c + c * a) ≥ a ^ 2 + b ^ 2 + c ^ 2 + a + b + c   :=  by sorry
