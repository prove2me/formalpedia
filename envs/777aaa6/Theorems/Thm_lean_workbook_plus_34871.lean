-- Prove2me | Theorems.Thm_lean_workbook_plus_34871
-- name    : lean_workbook_plus_34871
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/fc5b4594-dfef-4491-8c99-206d69ac0b6f
-- statement:
--   Show that $ \sum_{n=1}^{x} 2^{n - 1} = 2^{x} - 1 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34871 : ∀ x : ℕ, ∑ n in Finset.range x, 2^(n-1) = 2^x - 1   :=  by sorry
