-- Prove2me | Theorems.Thm_lean_workbook_plus_67665
-- name    : lean_workbook_plus_67665
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/5dcfedb0-d54b-45b3-b534-af11881dba19
-- statement:
--   (1) We have: $a+b+c=0$ , so $a^2+b^2+c^2=-2(ab+bc+ca)$ , so $(a^2+b^2+c^2)^2=4((ab)^2+(bc)^2+(ca)^2+2a^2bc+2ab^2c+2abc^2)=4((ab)^2+(bc)^2+(ca)^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67665  (a b c: ℝ)
  (h₀ : a + b + c = 0) :
  a^2 + b^2 + c^2 = -2 * (a * b + b * c + c * a)   :=  by sorry
