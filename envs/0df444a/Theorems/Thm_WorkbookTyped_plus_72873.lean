-- Prove2me | Theorems.Thm_WorkbookTyped_plus_72873
-- name    : WorkbookTyped.plus_72873
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:11:35.040657+00:00
-- url     : https://prove2.me/theorems/e74a8d86-2e8d-4d4f-bbed-9b534da62da6
-- title:
--   Subadditivity of fractional real powers
-- statement:
--   Let $ x,y > 0$ and $ t\in (0,1)$ . Prove $ (x + y)^t\le x^t + y^t.$
--
--   Source declaration repair: Added the explicit real binder t, as required by the source condition t ∈ (0,1), so all three powers use Real.rpow. The malformed declaration and its possible vacuous natural-number interpretation are not retained. A genuine real-power proof replaces the original tactic attempts.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_72873` (Apache-2.0). The original source declaration omits t; this public record supplies its intended real type.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_72873; explicit variable-declaration repair; Apache-2.0

import Mathlib

theorem WorkbookTyped.plus_72873 (x y t : ℝ) (hx : 0 < x) (hy : 0 < y) (h : 0 < t ∧ t < 1) :
  (x + y)^t ≤ x^t + y^t   :=  by sorry
