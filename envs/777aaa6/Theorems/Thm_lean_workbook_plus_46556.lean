-- Prove2me | Theorems.Thm_lean_workbook_plus_46556
-- name    : lean_workbook_plus_46556
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/0636d69c-cdde-4417-9931-195ed491855c
-- statement:
--   As: $(x+y+z)^3=x^3+y^3+z^3+3(x+y+z)(xy+yz+zx)-3xyz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46556 : ∀ x y z : ℝ, (x + y + z) ^ 3 = x ^ 3 + y ^ 3 + z ^ 3 + 3 * (x + y + z) * (xy + yz + zx) - 3 * x * y * z   :=  by sorry
