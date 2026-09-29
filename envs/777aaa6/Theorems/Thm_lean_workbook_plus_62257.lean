-- Prove2me | Theorems.Thm_lean_workbook_plus_62257
-- name    : lean_workbook_plus_62257
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/03e885f8-e168-4ac0-8468-aeecf2c56d74
-- statement:
--   Prove that $ x^{2}+y^{2}+z^{2}\ge xy+yz+zx$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62257 :  ∀ x y z : ℝ, x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + y * z + z * x   :=  by sorry
