-- Prove2me | Theorems.Thm_lean_workbook_plus_30282
-- name    : lean_workbook_plus_30282
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/f0f17dde-f158-45c5-ae4a-4336159eb7bd
-- statement:
--   Let $ x, \; y, \; z \in \mathbb{C}$ . We can use the following factorization: $ x^3 + y^3 + z^3 - 3xyz = (x + y + z)(x^2 + y^2 + z^2 - xy - yz - zx)$ . If $ x + y + z = 0$ , prove that $ x^3 + y^3 + z^3 = 3xyz$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30282 (x y z : ℂ) (h : x + y + z = 0) : x^3 + y^3 + z^3 = 3 * x * y * z   :=  by sorry
