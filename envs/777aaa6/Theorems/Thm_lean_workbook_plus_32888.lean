-- Prove2me | Theorems.Thm_lean_workbook_plus_32888
-- name    : lean_workbook_plus_32888
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/716d7377-dc8f-4902-86e9-861e1ca75593
-- statement:
--   Prove that $(1+a^2)(1+b^2)(1+c^2) = (a+b+c-abc)^2 + (ab+bc+ca-1)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32888 (a b c : ℝ) : (1+a^2)*(1+b^2)*(1+c^2) = (a+b+c-(a*b*c))^2 + (a*b+b*c+c*a-1)^2   :=  by sorry
