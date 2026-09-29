-- Prove2me | Theorems.Thm_lean_workbook_plus_61635
-- name    : lean_workbook_plus_61635
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/0618b393-e2f4-44b5-8de3-a29edf71a7b1
-- statement:
--   Let $ c^2 = 4a^2 - 4a - 4b^2$. Prove that $ c^2 + 1 = (2a - 1)^2 - 4b^2 = (2a - 2b - 1)(2a + 2b - 1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61635 ∀ a b c : ℤ,  c^2 = 4 * a^2 - 4 * a - 4 * b^2 → c^2 + 1 = (2 * a - 1)^2 - 4 * b^2 ∧ c^2 + 1 = (2 * a - 2 * b - 1) * (2 * a + 2 * b - 1)   :=  by sorry
