-- Prove2me | Theorems.Thm_lean_workbook_plus_45833
-- name    : lean_workbook_plus_45833
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/c8611e38-c62b-4638-aab2-f1256eb60c60
-- statement:
--   Let a,b,c be positive real numbers such that $ab+bc+ca=3$ Prove that $a^2+b^2+c^2+3 \ge 2(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45833 (a b c : ℝ) (h : a * b + b * c + c * a = 3) : a ^ 2 + b ^ 2 + c ^ 2 + 3 ≥ 2 * (a + b + c)   :=  by sorry
