-- Prove2me | Theorems.Thm_lean_workbook_plus_6462
-- name    : lean_workbook_plus_6462
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/909e1f4a-64dd-4d5d-96af-15dd5fefd411
-- statement:
--   Let $a,b \in R$ and satisfy $0 \le a \le b \le 1$ . Prove that: $ab^2-a^2b \le \frac{1}{4}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6462 (a b : ℝ) (h1 : 0 ≤ a ∧ 0 ≤ b) (h2 : a ≤ b) (h3 : b ≤ 1) : a * b^2 - a^2 * b ≤ 1 / 4   :=  by sorry
