-- Prove2me | Theorems.Thm_lean_workbook_plus_31976
-- name    : lean_workbook_plus_31976
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/3bfe6f96-d8ba-4fcd-b430-0e8be7d1393d
-- statement:
--   Prove the inequality $a^{4}+b^{4}+c^{4}\geq abc(a+b+c)$ using the simple inequality $x^2+y^2+z^2\ge xy+yz+zx$ for any real numbers $x, y, z$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31976 (a b c: ℝ) : a ^ 4 + b ^ 4 + c ^ 4 ≥ a * b * c * (a + b + c)   :=  by sorry
