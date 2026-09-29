-- Prove2me | Theorems.Thm_lean_workbook_plus_14481
-- name    : lean_workbook_plus_14481
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/0bc7f6ad-e4ea-430d-aec9-5eb3774e2f66
-- statement:
--   Show that $2 \nmid n^2 + n + 1$ for all positive integers $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14481 (n : ℕ) : ¬ 2 ∣ n^2 + n + 1   :=  by sorry
