-- Prove2me | Theorems.Thm_lean_workbook_plus_71001
-- name    : lean_workbook_plus_71001
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/3ae74a5c-ed13-4634-858f-10ed843070fb
-- statement:
--   Actually, its $a^{\phi(n)} \equiv 1 \mod n$ So, $11^{400}\equiv1 \mod 1000$ And so, $11^{1200}=(11^{400})^3\equiv1^3\equiv1 \mod 1000$ And so the last three digits are $001$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71001 11^1200 ≡ 1 [MOD 1000]   :=  by sorry
