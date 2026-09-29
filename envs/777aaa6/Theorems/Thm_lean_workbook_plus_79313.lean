-- Prove2me | Theorems.Thm_lean_workbook_plus_79313
-- name    : lean_workbook_plus_79313
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/c7f551af-db53-461c-818c-f754fe1d0381
-- statement:
--   Prove that for all reals $x$ , $y$ , $z$, $x^2 + y^2 + z^2 \geq \frac{1}{3}(x+y+z)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_79313 (x y z: ℝ) : x ^ 2 + y ^ 2 + z ^ 2 ≥ 1 / 3 * (x + y + z) ^ 2   :=  by sorry
