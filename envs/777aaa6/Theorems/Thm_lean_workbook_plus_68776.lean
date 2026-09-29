-- Prove2me | Theorems.Thm_lean_workbook_plus_68776
-- name    : lean_workbook_plus_68776
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/5f367e58-3cd1-41ed-9c1e-aeea973a7f31
-- statement:
--   Prove that $ 3(x^2 + y^2 + z^2)\geq (x + y + z)^2$ using Cauchy-Schwarz inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68776 {x y z : ℝ} : 3 * (x ^ 2 + y ^ 2 + z ^ 2) ≥ (x + y + z) ^ 2   :=  by sorry
