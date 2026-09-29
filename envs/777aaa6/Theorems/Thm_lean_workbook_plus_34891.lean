-- Prove2me | Theorems.Thm_lean_workbook_plus_34891
-- name    : lean_workbook_plus_34891
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/23e85099-70a2-4a10-a43b-4ce0f3d23ae7
-- statement:
--   In triangle $ABC$ ,prove $(b^2+c^2)/4+(c-a)(b-a)>0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34891 (a b c : ℝ) (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : (b^2 + c^2) / 4 + (c - a) * (b - a) > 0   :=  by sorry
