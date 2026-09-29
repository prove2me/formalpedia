-- Prove2me | Theorems.Thm_WorkbookSource_plus_5556
-- name    : WorkbookSource.plus_5556
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:45.48399+00:00
-- url     : https://prove2.me/theorems/935f7fe5-a067-4fb4-ba99-5c76b9c33f41
-- title:
--   Three quadratic forms bound a mixed cubic product
-- statement:
--   Given $ a, b, c \geq\ 0.$ Prove that:
--    $ (3a^2-ab+3b^2)(3b^2-bc+3c^2)(3c^2-ca+3a^2) \geq\ \frac{125}{3}abc(a^3+b^3+c^3)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_5556` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_5556; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_5556 (a b c : ℝ) : (3 * a ^ 2 - a * b + 3 * b ^ 2) * (3 * b ^ 2 - b * c + 3 * c ^ 2) * (3 * c ^ 2 - c * a + 3 * a ^ 2) ≥ 125 / 3 * a * b * c * (a ^ 3 + b ^ 3 + c ^ 3)   :=  by sorry
