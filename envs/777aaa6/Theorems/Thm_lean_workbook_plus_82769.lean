-- Prove2me | Theorems.Thm_lean_workbook_plus_82769
-- name    : lean_workbook_plus_82769
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/75d4f2f7-e7d7-4cdb-8117-d165b2264f9d
-- statement:
--   Let $a$ be positive real numbers such that $a^3-a-2=0$ . Prove that $\sqrt[4]{5}<a<2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82769 (a : ℝ) (ha : a^3 - a - 2 = 0) : (5:ℝ)^(1/4) < a ∧ a < 2   :=  by sorry
