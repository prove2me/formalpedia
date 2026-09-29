-- Prove2me | Theorems.Thm_lean_workbook_plus_5639
-- name    : lean_workbook_plus_5639
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/5a8b200c-031a-4128-b286-aa399911b94f
-- statement:
--   Prove that $n^7-n$ is divisible by 3 when $n\equiv 0$ mod $3$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5639 (n : ℤ) (h : n ≡ 0 [ZMOD 3]) : n ^ 7 - n ≡ 0 [ZMOD 3]   :=  by sorry
