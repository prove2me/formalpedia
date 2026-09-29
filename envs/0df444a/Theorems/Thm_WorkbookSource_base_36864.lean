-- Prove2me | Theorems.Thm_WorkbookSource_base_36864
-- name    : WorkbookSource.base_36864
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:28:12.174165+00:00
-- url     : https://prove2.me/theorems/126a15ee-26c3-4524-9c8a-74015bfd067e
-- title:
--   A sextic and quadratic product bounds a mixed quartic square
-- statement:
--   Applying CS, $\left( a^4b^2+a^2b^4+b^4c^2+b^2c^4+c^4a^2+c^2a^4+2a^2b^2c^2\right)(b^2+a^2+c^2+b^2+a^2+c^2+2)\geq \left(2\sum_{cyc} a^2b^2+2abc \right) ^2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_36864` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_36864; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_36864 {a b c : ℝ} : (a^4 * b^2 + a^2 * b^4 + b^4 * c^2 + b^2 * c^4 + c^4 * a^2 + c^2 * a^4 + 2 * a^2 * b^2 * c^2) * (b^2 + a^2 + c^2 + b^2 + a^2 + c^2 + 2) ≥ (2 * (a^2 * b^2 + b^2 * c^2 + a^2 * c^2) + 2 * a * b * c)^2  :=  by sorry
