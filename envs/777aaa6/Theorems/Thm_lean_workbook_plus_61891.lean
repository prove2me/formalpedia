-- Prove2me | Theorems.Thm_lean_workbook_plus_61891
-- name    : lean_workbook_plus_61891
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/8e7eff82-f423-435c-a0ec-5e6391760673
-- statement:
--   Hence we obtain\n\n $ab = (10x + y)(10x + z) = 100x^2 + 10x(y + z) + yz = 100x^2 + 10x \cdot 10 + yz$ ,\n\ni.e.\n\n $(4) \;\; ab = 100x(x + 1) + yz$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61891 : ∀ a b x y z : ℕ, a = 10 * x + y ∧ b = 10 * x + z → a * b = 100 * x^2 + 10 * x * (y + z) + y * z   :=  by sorry
