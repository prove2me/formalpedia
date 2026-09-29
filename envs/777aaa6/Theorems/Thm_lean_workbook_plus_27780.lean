-- Prove2me | Theorems.Thm_lean_workbook_plus_27780
-- name    : lean_workbook_plus_27780
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/3698ffd9-80d0-499b-a9cb-cc21bad733b8
-- statement:
--   But, also, since we assumed $ z = min(x,y,z)$ , and all are positive, we know that $ z\le \dfrac{1}{3}$ Therefore, the expression becomes: $ \dfrac{\sqrt {2}}{2} \ge \dfrac{\dfrac{1}{3}}{\dfrac{\sqrt {2}}{3}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27780 : (Real.sqrt 2 / 2) ≥ (1 / 3) / (Real.sqrt 2 / 3)   :=  by sorry
