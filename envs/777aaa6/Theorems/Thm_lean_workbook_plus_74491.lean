-- Prove2me | Theorems.Thm_lean_workbook_plus_74491
-- name    : lean_workbook_plus_74491
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e9968332-cffc-437a-8f2a-cd718e39b73d
-- statement:
--   $ \frac {{a\left( {a - b} \right)\left( {a - c} \right)}}{{a^2 + 2bc}} + \frac {{b\left( {b - a} \right)\left( {b - c} \right)}}{{b^2 + 2ca}} = \frac {{\left( {a - b} \right)^2 \left( {2a^2 c + 2b^2 c + abc - ac^2 - bc^2 } \right)}}{{\left( {a^2 + 2bc} \right)\left( {b^2 + 2ca} \right)}} \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74491 :
  ∀ a b c : ℝ,
    (a * (a - b) * (a - c)) / (a^2 + 2 * b * c) + (b * (b - a) * (b - c)) / (b^2 + 2 * c * a) =
      (a - b)^2 * (2 * a^2 * c + 2 * b^2 * c + a * b * c - a * c^2 - b * c^2) / ((a^2 + 2 * b * c) * (b^2 + 2 * c * a)) ∧
    (a - b)^2 * (2 * a^2 * c + 2 * b^2 * c + a * b * c - a * c^2 - b * c^2) / ((a^2 + 2 * b * c) * (b^2 + 2 * c * a)) ≥ 0   :=  by sorry
