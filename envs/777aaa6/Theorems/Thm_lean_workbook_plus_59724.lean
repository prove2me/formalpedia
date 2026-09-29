-- Prove2me | Theorems.Thm_lean_workbook_plus_59724
-- name    : lean_workbook_plus_59724
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/0c40c435-702b-4133-8baa-1048cbab523a
-- statement:
--   Triangle numbers and their relation to perfect squares: $\dfrac{n(n + 1)}{2} = \dfrac{(2n + 1)^2 - 1}{8}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59724 (n : ℕ) : (n * (n + 1)) / 2 = ((2 * n + 1)^2 - 1) / 8   :=  by sorry
