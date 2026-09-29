-- Prove2me | Theorems.Thm_lean_workbook_plus_72320
-- name    : lean_workbook_plus_72320
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/a8ce7cc8-29b1-4e77-b2ec-9eda7a66dbfe
-- statement:
--   Its domain is $x: 9x^2 \geq 18x$ . All $x \leq 0$ satisfy this, as does $x \geq 2$ . For $0<x<2$ , the function $f$ has complex values.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72320 (∀ x, 9*x^2 >= 18*x ↔ x <= 0 ∨ x >= 2)   :=  by sorry
