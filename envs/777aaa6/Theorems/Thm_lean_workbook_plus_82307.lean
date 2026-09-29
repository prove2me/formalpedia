-- Prove2me | Theorems.Thm_lean_workbook_plus_82307
-- name    : lean_workbook_plus_82307
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/b70351cb-c1fe-4dfb-843e-1c364ffef53d
-- statement:
--   Calculate $\binom{20}{3}$ using the factorial formula.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82307 (h₁ : 3 ≤ 20) : (Nat.choose 20 3 : ℚ) = (20! / (17! * 3!))   :=  by sorry
