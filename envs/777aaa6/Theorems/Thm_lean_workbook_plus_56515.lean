-- Prove2me | Theorems.Thm_lean_workbook_plus_56515
-- name    : lean_workbook_plus_56515
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/62b3c8e2-c105-459c-a043-b4b4c6250100
-- statement:
--   Prove $a^2b+b^2c+c^2a \le \sqrt{(a^2+b^2+c^2)(a^2b^2+b^2c^2+c^2a^2) }$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56515 :
  ∀ a b c : ℝ,
    a^2 * b + b^2 * c + c^2 * a ≤ Real.sqrt ((a^2 + b^2 + c^2) * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2))   :=  by sorry
