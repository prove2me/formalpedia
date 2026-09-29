-- Prove2me | Theorems.Thm_WorkbookSource_problem_34538
-- name    : WorkbookSource.problem_34538
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:59:57.092829+00:00
-- url     : https://prove2.me/theorems/7050a718-e7d4-44de-b33f-806eec064940
-- title:
--   A cyclic sum of quadratic squares
-- statement:
--   For real numbers $a,b,c$,
--
--   $$\left(a^2-ab+b^2-\frac{a+b}{2}\right)^2+\left(b^2-bc+c^2-\frac{b+c}{2}\right)^2+\left(c^2-ca+a^2-\frac{c+a}{2}\right)^2\ge0.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34538` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34538; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_34538 (a b c : ℝ) : (a^2 - a * b + b^2 - (a + b) / 2)^2 + (b^2 - b * c + c^2 - (b + c) / 2)^2 + (c^2 - c * a + a^2 - (c + a) / 2)^2 ≥ 0  :=  by sorry
