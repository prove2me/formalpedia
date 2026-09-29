-- Prove2me | Theorems.Thm_lean_workbook_plus_35447
-- name    : lean_workbook_plus_35447
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/9548e06b-f020-4eda-bfff-badd82f5a38d
-- statement:
--   In triangle, prove that:\n\n $\left( {\frac {{\it w_a}}{{\it h_a}}}+{\frac {{\it h_a}}{{\it w_a}}} \right) \left( {\frac {{\it w_b}}{{\it h_b}}}+{\frac {{\it h_b}}{{\it w_b}}} \right) \left( {\frac {{\it w_c}}{{\it h_c}}}+{\frac {{\it h_c}}{{\it w_c}}} \right) \geq {\frac {8}{9}}\, \left( {\frac {{\it w_a}}{{\it h_a}}}+{\frac {{\it w_b}}{{\it h_b}}}+{\frac {{\it w_c}}{{\it h_c}}} \right) \left( {\frac {{\it h_a}}{{\it w_a}}}+{\frac {{\it h_b}}{{\it w_b}}}+{\frac {{\it h_c}}{{\it w_c}}} \right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35447 : ∀ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b > c ∧ a + c > b ∧ b + c > a → (wa / ha + ha / wa) * (wb / hb + hb / wb) * (wc / hc + hc / wc) ≥ 8 / 9 * (wa / ha + wb / hb + wc / hc) * (ha / wa + hb / hb + hc / wc)   :=  by sorry
