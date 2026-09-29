-- Prove2me | Theorems.Thm_lean_workbook_plus_59225
-- name    : lean_workbook_plus_59225
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/6ddcd42e-60b5-429b-b26a-2daa067c1d79
-- statement:
--   The answer is $\binom{9}{3} \cdot \binom{6}{3} \cdot \binom{3}{3} = 1680$ since out of thee $9$ times you move you need to choose $3$ moves in the $z$ direction, $3$ moves in the $y$ direction and $3$ moves in the $x$ direction.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59225 (Nat.choose 9 3 * Nat.choose 6 3 * Nat.choose 3 3) = 1680   :=  by sorry
