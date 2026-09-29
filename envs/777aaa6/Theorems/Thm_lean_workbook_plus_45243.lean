-- Prove2me | Theorems.Thm_lean_workbook_plus_45243
-- name    : lean_workbook_plus_45243
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/0c79a660-b4f3-41ae-95c3-9e67ed30ac9a
-- statement:
--   For any positive integer $ m$, prove that $ m$ and $ m + 1$ are relatively prime.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45243 (m : ℕ) : Nat.Coprime m (m + 1)   :=  by sorry
