-- Prove2me | Theorems.Thm_lean_workbook_plus_53786
-- name    : lean_workbook_plus_53786
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/5acaaf8c-3663-46ef-890d-6f56ddb4c885
-- statement:
--   WLOG let $ a\ge b\ge c$ . Then we have to show that $ a^2 + b^2 + c^2\ge\sqrt 3(a^2 - c^2)$ , which is equivalent to $ b^2 + (\sqrt 3 + 1)c^2\ge (\sqrt 3 - 1)a^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53786 :
  ∀ a b c : ℝ, a ≥ b ∧ b ≥ c → a^2 + b^2 + c^2 ≥ Real.sqrt 3 * (a^2 - c^2)   :=  by sorry
