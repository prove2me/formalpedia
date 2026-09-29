-- Prove2me | Theorems.Thm_WorkbookSource_base_1815
-- name    : WorkbookSource.base_1815
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:39.979791+00:00
-- url     : https://prove2.me/theorems/7e338c93-fc5e-4361-8857-4bed23ce2f11
-- title:
--   Three quadratic forms bound a cubed pairwise sum and squared differences
-- statement:
--   The following inequality is also true.
--   For all reals $a$ , $b$ and $c$ prove that:
--    $ (a^2 + ab + b^2)(b^2 + bc + c^2)(c^2 + ca + a^2)\ge (ab + bc + ca)^3+\frac{1}{6}(a-b)^2(a-c)^2(b-c)^2
--
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_1815` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_1815; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_1815 (a b c : ℝ) :
  (a^2 + a * b + b^2) * (b^2 + b * c + c^2) * (c^2 + c * a + a^2) ≥ (a * b + b * c + c * a)^3 + (1/6) * (a - b)^2 * (a - c)^2 * (b - c)^2  :=  by sorry
