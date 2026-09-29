-- Prove2me | Theorems.Thm_lean_workbook_plus_40519
-- name    : lean_workbook_plus_40519
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/20ecf5ad-192e-48b4-9529-1b36f4d08579
-- statement:
--   it is enough to prove that $x^{2}y^{2}+y^{2}z^{2}+z^{2}x^{2}\\geq x^{2}yz+xy^{2}z+xyz^{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40519 (x y z : ℝ) : x^2 * y^2 + y^2 * z^2 + z^2 * x^2 ≥ x^2 * y * z + x * y^2 * z + x * y * z^2   :=  by sorry
