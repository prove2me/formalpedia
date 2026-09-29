-- Prove2me | Theorems.Thm_lean_workbook_plus_36538
-- name    : lean_workbook_plus_36538
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/45829ef6-9cec-4d8f-a787-9b93b918bc23
-- statement:
--   What you actually want is ${n \choose 0} + {n + 1 \choose 1} + ... + {n + r \choose r} = {n + r + 1 \choose r}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36538 (n r : ℕ) : ∑ k in Finset.range (r + 1), choose (n + k) k = choose (n + r + 1) r   :=  by sorry
