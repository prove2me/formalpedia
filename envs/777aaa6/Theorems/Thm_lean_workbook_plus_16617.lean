-- Prove2me | Theorems.Thm_lean_workbook_plus_16617
-- name    : lean_workbook_plus_16617
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/cdbb1a9c-b34f-45f4-8c8b-188a3d4c4518
-- statement:
--   Substituting $d=-a-b-c$ , we wish to show $a^3+b^3+c^3-(a+b+c)^3 =3(abc-(a+b+c)ab -(a+b+c)bc-(a+b+c)ca)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16617 (a b c d : ℝ) (h₁ : d = -a - b - c) :
  a^3 + b^3 + c^3 - (a + b + c)^3 =
    3 * (a * b * c - (a + b + c) * a * b - (a + b + c) * b * c - (a + b + c) * c * a)   :=  by sorry
