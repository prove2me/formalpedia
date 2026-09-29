-- Prove2me | Theorems.Thm_lean_workbook_plus_73006
-- name    : lean_workbook_plus_73006
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/24cf9622-5bbb-4c25-b422-8b2beebfe444
-- statement:
--   Prove that $x^2+y^2+z^2\geq xy+xz+yz$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73006 : ∀ (x y z : ℝ), x ^ 2 + y ^ 2 + z ^ 2 ≥ x * y + x * z + y * z   :=  by sorry
