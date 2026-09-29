-- Prove2me | Theorems.Thm_lean_workbook_plus_37870
-- name    : lean_workbook_plus_37870
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/31c615a3-7758-4cda-ae54-1ae5a79d286a
-- statement:
--   Prove that $abc \le 1$ implies $a^2b^2c^2+abc +abc(ab+bc+ca)+abc(a+b+c) \le a^2+b^2+c^2 +a+b+c+2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37870 :  ∀ a b c : ℝ, a * b * c ≤ 1 → a^2 * b^2 * c^2 + a * b * c + a * b * c * (a * b + b * c + c * a) + a * b * c * (a + b + c) ≤ a^2 + b^2 + c^2 + a + b + c + 2   :=  by sorry
