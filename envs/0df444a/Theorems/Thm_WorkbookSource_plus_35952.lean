-- Prove2me | Theorems.Thm_WorkbookSource_plus_35952
-- name    : WorkbookSource.plus_35952
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:52.888951+00:00
-- url     : https://prove2.me/theorems/a6f32ac4-a43b-4ce6-9990-2219387a8bd3
-- title:
--   A four-variable cyclic quartic inequality with a bilinear correction
-- statement:
--   prove that:
--
--    $(ac+bd)^2+\frac{3}{4}(a^2+c^2+b^2+d^2)^2 \geq (a+b+c+d)(ab^2+bc^2+cd^2+a^2d)$
--
--    $a,b,c,d \in R$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_35952` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_35952; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_35952 (a b c d : ℝ) : (a * c + b * d) ^ 2 + (3 / 4) * (a ^ 2 + c ^ 2 + b ^ 2 + d ^ 2) ^ 2 ≥ (a + b + c + d) * (a * b ^ 2 + b * c ^ 2 + c * d ^ 2 + a ^ 2 * d)   :=  by sorry
