-- Prove2me | Theorems.Thm_lean_workbook_plus_20958
-- name    : lean_workbook_plus_20958
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/d24f9d99-7f76-4a05-bad4-9d891ae6c545
-- statement:
--   If $a+11=4^2*5$ , and $b+80=10^2*5$ , then what is $1000a+b$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20958 (a b : ℕ) (h₁ : a + 11 = 4^2 * 5) (h₂ : b + 80 = 10^2 * 5) : 1000 * a + b = 1000 * 4^2 * 5 - 11 * 1000 + 10^2 * 5 - 80   :=  by sorry
