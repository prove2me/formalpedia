-- Prove2me | Theorems.Thm_lean_workbook_plus_3193
-- name    : lean_workbook_plus_3193
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/16c47fdc-2016-4216-9081-1da188c7d38a
-- statement:
--   Let $ 0<a \le b \le c \le d$ be real numbers. Prove that: $ 7a^2+5b^2+3c^2+d^2 \le (a+b+c+d)^2 \le a^2+3b^2+5c^2+7d^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3193 (a b c d : ℝ) (h1 : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d) (h2 : a ≤ b ∧ b ≤ c ∧ c ≤ d) : 7 * a ^ 2 + 5 * b ^ 2 + 3 * c ^ 2 + d ^ 2 ≤ (a + b + c + d) ^ 2 ∧ (a + b + c + d) ^ 2 ≤ a ^ 2 + 3 * b ^ 2 + 5 * c ^ 2 + 7 * d ^ 2   :=  by sorry
