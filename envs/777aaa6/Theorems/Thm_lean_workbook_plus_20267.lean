-- Prove2me | Theorems.Thm_lean_workbook_plus_20267
-- name    : lean_workbook_plus_20267
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/bd6178b1-1eba-4518-98d9-2f4a625a97c8
-- statement:
--   The inequality is obvious for $n=1$ , since the left side is just $1$ . For $n=2$ , the inequality reads $2^{64}\leq 64!$ , which is obvious from $64!\geq 64^{32}=2^{6\times 32}>2^{64}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20267 : (2^(64:ℕ)) ≤ 64!   :=  by sorry
