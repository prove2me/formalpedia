-- Prove2me | Theorems.Thm_lean_workbook_plus_20949
-- name    : lean_workbook_plus_20949
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/f1e855ea-35b6-466b-9ef4-efe298eb51a1
-- statement:
--   Prove that $ 4(a+b+c)^6 \ge 27(ab+bc+ca)(a^2+b^2+c^2+ab+bc+ca)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20949 : ∀ a b c : ℝ, 4 * (a + b + c) ^ 6 ≥ 27 * (a * b + b * c + c * a) * (a ^ 2 + b ^ 2 + c ^ 2 + a * b + b * c + c * a) ^ 2   :=  by sorry
