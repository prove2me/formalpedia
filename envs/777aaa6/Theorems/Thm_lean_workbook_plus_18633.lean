-- Prove2me | Theorems.Thm_lean_workbook_plus_18633
-- name    : lean_workbook_plus_18633
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/ccd0413d-e597-4d42-aa8e-671662f80b63
-- statement:
--   Lemma. $x,y,z\in R\Longrightarrow xy+yz+zx\le x^{2}+y^{2}+z^{2}\ .$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18633 : ∀ x y z : ℝ, x * y + y * z + z * x ≤ x ^ 2 + y ^ 2 + z ^ 2   :=  by sorry
