-- Prove2me | Theorems.Thm_lean_workbook_plus_30881
-- name    : lean_workbook_plus_30881
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/ca4312e4-b271-4b0a-aa23-3bc1bf0cf7ac
-- statement:
--   If $ a,\ b,\ c \geq 1$ , show that $ 4(abc+1) \geq (a+1)(b+1)(c+1)$ . When do we have equality?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30881 (a b c : ℝ) (ha : a ≥ 1) (hb : b ≥ 1) (hc : c ≥ 1) : 4 * (a * b * c + 1) ≥ (a + 1) * (b + 1) * (c + 1)   :=  by sorry
