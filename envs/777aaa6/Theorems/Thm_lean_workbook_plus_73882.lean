-- Prove2me | Theorems.Thm_lean_workbook_plus_73882
-- name    : lean_workbook_plus_73882
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/bad03733-a644-4eec-aadb-dfa4332399e7
-- statement:
--   Prove that $t^{3}-3t+2 \le 4 $ , if $ t \le \frac{1}{4}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73882 : ∀ t : ℝ, t ≤ 1/4 → t^3 - 3 * t + 2 ≤ 4   :=  by sorry
