-- Prove2me | Theorems.Thm_lean_workbook_plus_34508
-- name    : lean_workbook_plus_34508
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/93f917fb-ec95-4e66-bc87-d1c4053d0add
-- statement:
--   Verify it for $n=2$ ; indeed we have $ \sqrt{\frac{1}{5}} < \frac{1}{2} < \sqrt{\frac{1}{3}} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34508 : ∀ n : ℕ, n = 2 → Real.sqrt (1 / 5) < 1 / 2 ∧ 1 / 2 < Real.sqrt (1 / 3)   :=  by sorry
