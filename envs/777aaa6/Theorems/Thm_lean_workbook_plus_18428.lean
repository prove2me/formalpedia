-- Prove2me | Theorems.Thm_lean_workbook_plus_18428
-- name    : lean_workbook_plus_18428
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/baeda44b-f4a9-4ea0-8f14-7846e65ced05
-- statement:
--   Prove: $LHS-RHS=(1/126)*(21*a^2+7*a*b-17*a*c-21*b^2+10*b*c)^2+(1/126)*(-17*a*b+10*a*c+21*b^2+7*b*c-21*c^2)^2+(1/126)*(-21*a^2+10*a*b+7*a*c-17*b*c+21*c^2)^2+(263/9198)*(7*a*b-17*a*c+10*b*c)^2+(263/9198)*(-17*a*b+10*a*c+7*b*c)^2+(263/9198)*(10*a*b+7*a*c-17*b*c)^2\ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18428 {a b c : ℝ} :
  (1 / 126) * (21 * a ^ 2 + 7 * a * b - 17 * a * c - 21 * b ^ 2 + 10 * b * c) ^ 2 + (1 / 126) * (-17 * a * b + 10 * a * c + 21 * b ^ 2 + 7 * b * c - 21 * c ^ 2) ^ 2 + (1 / 126) * (-21 * a ^ 2 + 10 * a * b + 7 * a * c - 17 * b * c + 21 * c ^ 2) ^ 2 + (263 / 9198) * (7 * a * b - 17 * a * c + 10 * b * c) ^ 2 + (263 / 9198) * (-17 * a * b + 10 * a * c + 7 * b * c) ^ 2 + (263 / 9198) * (10 * a * b + 7 * a * c - 17 * b * c) ^ 2 ≥ 0   :=  by sorry
