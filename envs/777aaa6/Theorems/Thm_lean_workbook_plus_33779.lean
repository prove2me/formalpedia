-- Prove2me | Theorems.Thm_lean_workbook_plus_33779
-- name    : lean_workbook_plus_33779
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/4847902d-8da4-4021-8434-141b9222137b
-- statement:
--   If $ 4n + 3|4k^2 + 1$ , then $ 4n + 3|4k^2 + 1 - (4n + 3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33779 (n k : ℤ) : 4 * n + 3 ∣ 4 * k ^ 2 + 1 → 4 * n + 3 ∣ 4 * k ^ 2 + 1 - (4 * n + 3)   :=  by sorry
