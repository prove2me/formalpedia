-- Prove2me | Theorems.Thm_lean_workbook_plus_11792
-- name    : lean_workbook_plus_11792
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/2b6ea274-2802-4da9-9af6-1f9ecdeef279
-- statement:
--   Prove that $ n^3 + (n + 1)^3 + (n + 2)^3$ is divisible by $ 9$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11792 : ∀ n : ℕ, 9 ∣ n^3 + (n + 1)^3 + (n + 2)^3   :=  by sorry
