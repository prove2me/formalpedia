-- Prove2me | Theorems.Thm_WorkbookSource_problem_51944
-- name    : WorkbookSource.problem_51944
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:09:08.397748+00:00
-- url     : https://prove2.me/theorems/f47bb29f-09d3-45ce-bcb4-c1e3c0aeea44
-- title:
--   A rational polynomial disjunction
-- statement:
--   2) $3/2 < p < 2$ : Using $r \ge \frac{5p^2q - p^4 - 4q^2}{6p}$ (4 degree Schur), we have $1 - q - 2 \cdot \frac{5p^2q - p^4 - 4q^2}{6p} \ge 0$ or $4\left(\frac58 p^2 + \frac38 p - q\right)^2 - \frac{3}{16}p(p - 1)(3p^2 + 13p + 16) \ge 0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_51944` (Apache-2.0). The complete source proposition and explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_51944; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_51944 (p q : ℝ) (hp : 3 / 2 < p ∧ p < 2) (hq : q = 1 - p) : (3 / 2 < p ∧ p < 2 ∧ 1 - q - 2 * (5 * p^2 * q - p^4 - 4 * q^2) / (6 * p) ≥ 0) ∨ (4 * (5 / 8 * p^2 + 3 / 8 * p - q)^2 - 3 / 16 * p * (p - 1) * (3 * p^2 + 13 * p + 16) ≥ 0)  :=  by sorry
