-- Prove2me | Theorems.Thm_lean_workbook_plus_13440
-- name    : lean_workbook_plus_13440
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/2da952fe-a060-424a-bdbc-f052a881a23f
-- statement:
--   Find the value of $\dbinom612^1+\dbinom622^2+\dbinom632^3+\dbinom642^4+\dbinom652^5+\dbinom662^6.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13440 (h₁ : 0 < 6) : (Nat.choose 6 1 * 2 ^ 1 + Nat.choose 6 2 * 2 ^ 2 + Nat.choose 6 3 * 2 ^ 3 + Nat.choose 6 4 * 2 ^ 4 + Nat.choose 6 5 * 2 ^ 5 + Nat.choose 6 6 * 2 ^ 6) = 728   :=  by sorry
