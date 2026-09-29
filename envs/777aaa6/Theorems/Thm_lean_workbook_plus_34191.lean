-- Prove2me | Theorems.Thm_lean_workbook_plus_34191
-- name    : lean_workbook_plus_34191
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/02249f2a-f8ac-4999-8b7e-34966b4affe6
-- statement:
--   For $ n>=1$ show by induction that \n\na) $ 15|2^{4n} - 1$ \nb) $ 5|3^{3n + 1} + 2^{n + 1}$ \nc) $ 24|2(7^n) + 3(5^n) - 5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34191 (n : ℕ) (hn : 1 ≤ n) : 15 ∣ 2 ^ (4 * n) - 1   :=  by sorry
