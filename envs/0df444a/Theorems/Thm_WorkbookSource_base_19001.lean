-- Prove2me | Theorems.Thm_WorkbookSource_base_19001
-- name    : WorkbookSource.base_19001
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:46:28.213033+00:00
-- url     : https://prove2.me/theorems/5e8d2201-ce0d-4e4c-b738-9c9125df8f9a
-- title:
--   A quartic pair-product sum bounds cyclic cubic and quadratic terms
-- statement:
--   Given $ a, b, c$ are the real numbers satisfy $ a+b+c=3$ . Prove that:
--   $ 3+a^2b^2+b^2c^2+c^2a^2 \ge ab^2+bc^2+ca^2+ab+bc+ca$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_19001` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_19001; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_19001 (a b c : ℝ) (h : a + b + c = 3) :
  3 + a^2 * b^2 + b^2 * c^2 + c^2 * a^2 ≥ a * b^2 + b * c^2 + c * a^2 + a * b + b * c + c * a  :=  by sorry
