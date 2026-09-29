-- Prove2me | Theorems.Thm_lean_workbook_plus_64443
-- name    : lean_workbook_plus_64443
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/9c2d25de-9d2e-4483-90e0-ce6cfe4434b9
-- statement:
--   By principle of inclusion and exclusion, required no. of ways= $\frac{10!}{2!^3}-\binom{3}{1}\frac{9!}{2!^2}+\binom{3}{2}\frac{8!}{2!}-\binom{3}{3}7!=\boxed{236880}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64443 :
  10! / 2!^3 - 3 * 9! / 2!^2 + 3 * 8! / 2! - 7! = 236880   :=  by sorry
