-- Prove2me | Theorems.Thm_lean_workbook_plus_80876
-- name    : lean_workbook_plus_80876
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/84ac56df-c784-4ccc-a437-5c2fd9482d02
-- statement:
--   In (2): $-b^{2}+c^{2}+p^{2} = 2p^{2} \rightarrow -b^{2}+c^{2}= p^{2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_80876 (b c p : ℝ) (h₁ : -b^2 + c^2 + p^2 = 2 * p^2) : -b^2 + c^2 = p^2   :=  by sorry
