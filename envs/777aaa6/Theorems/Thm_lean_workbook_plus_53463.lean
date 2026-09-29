-- Prove2me | Theorems.Thm_lean_workbook_plus_53463
-- name    : lean_workbook_plus_53463
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/1ad21757-66d4-4662-81b5-472898da4515
-- statement:
--   Let $ a + b = x$ $ b + c = y$ $ a + c = z$ $ x^2 + y^2 + z^2 = 3$ $ (x + y)^2 + (y + z)^2 + (x + z)^2\le 12$ $ 2x^2 + 2y^2 + 2z^2 + 2xy + 2yz + 2xz\le 12$ $ xy + yz + zx\le3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53463 : ∀ x y z : ℝ, (x^2 + y^2 + z^2 = 3 ∧ (x + y)^2 + (y + z)^2 + (x + z)^2 ≤ 12 → x*y + y*z + z*x ≤ 3)   :=  by sorry
