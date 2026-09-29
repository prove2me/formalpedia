-- Prove2me | Theorems.Thm_lean_workbook_plus_74328
-- name    : lean_workbook_plus_74328
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/dae46e08-5a51-4d2f-9f63-baf7a78db2a9
-- statement:
--   $f(1)=f(1)^2$ and so $f(1)\in\{0,1\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74328 {f : ℕ → ℕ} (h : f 1 = f 1 ^ 2) : f 1 = 0 ∨ f 1 = 1   :=  by sorry
