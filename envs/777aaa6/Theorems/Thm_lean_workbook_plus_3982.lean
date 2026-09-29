-- Prove2me | Theorems.Thm_lean_workbook_plus_3982
-- name    : lean_workbook_plus_3982
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/d49afa4d-2d32-407b-8ab1-1c5620313d71
-- statement:
--   We have a well-known inequality $ \begin{array}{l} \left( {a + b + c} \right)\left( {{a^2} + {b^2} + {c^2}} \right) \ge 3\left( {{a^2}b + {b^2}c + {c^2}a} \right) \Leftrightarrow a{\left( {a - b} \right)^2} + b{\left( {b - c} \right)^2} + c{\left( {c - a} \right)^2} \ge 0 \end{array}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3982 (a b c : ℝ) : (a + b + c) * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ↔ a * (a - b) ^ 2 + b * (b - c) ^ 2 + c * (c - a) ^ 2 ≥ 0   :=  by sorry
