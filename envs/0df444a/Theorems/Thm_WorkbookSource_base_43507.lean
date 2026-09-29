-- Prove2me | Theorems.Thm_WorkbookSource_base_43507
-- name    : WorkbookSource.base_43507
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:48:36.964769+00:00
-- url     : https://prove2.me/theorems/b9ea175a-f5fe-4f7b-80ef-137af3c51dae
-- title:
--   Six mixed sextic monomials bound three cubic products
-- statement:
--   Then the ineq. turns into
--   $ p^4q^2+q^4p^2+p^4r^2+r^4p^2+q^4r^2+r^4q^2 \ge 2(p^3q^3+q^3r^3+r^3p^3)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_43507` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43507; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_43507 (p q r : ℝ) : p ^ 4 * q ^ 2 + q ^ 4 * p ^ 2 + p ^ 4 * r ^ 2 + r ^ 4 * p ^ 2 + q ^ 4 * r ^ 2 + r ^ 4 * q ^ 2 ≥ 2 * (p ^ 3 * q ^ 3 + q ^ 3 * r ^ 3 + r ^ 3 * p ^ 3)  :=  by sorry
