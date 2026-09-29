-- Prove2me | Theorems.Thm_lean_workbook_plus_29927
-- name    : lean_workbook_plus_29927
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/9ecf2faa-a449-45cb-ad5a-6a4e980e7efb
-- statement:
--   Let $x, y, z$ be nonnegative positive integers. Prove that \n $$\frac{x}{zx+2x+1} + \frac{y}{xy+2y+1} + \frac{z}{yz+2z+1}\leq\frac{3}{4}\leq\frac{x}{xy+2y+1}+\frac{y}{yz+2z+1}+\frac{z}{zx+2x+1}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29927 (x y z : ℕ) : (x / (z * x + 2 * x + 1) + y / (x * y + 2 * y + 1) + z / (y * z + 2 * z + 1) ≤ 3 / 4 ∧ 3 / 4 ≤ x / (x * y + 2 * y + 1) + y / (y * z + 2 * z + 1) + z / (z * x + 2 * x + 1))   :=  by sorry
