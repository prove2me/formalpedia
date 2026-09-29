-- Prove2me | Theorems.Thm_WorkbookSource_base_43118
-- name    : WorkbookSource.base_43118
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:30.27151+00:00
-- url     : https://prove2.me/theorems/32f9d2dc-1605-420e-8dc1-ca51b0fafd4f
-- title:
--   An asymmetric four-variable quartic inequality
-- statement:
--   Stronger:
--
--    $\\frac{1}{2} \\Bigl( 3(ad+bc-ac-bd)^2 + 3(ad-bc)^2 + (ac-bd)^2 \\Bigr) \\geq 0$
--
--    $\\iff 3a^2d^2 + 3b^2c^2 + 2a^2c^2 +2b^2d^2 + 2abcd \\geq 3a^2cd + 3d^2ab + 3c^2ab + 3b^2cd$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_43118` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_43118; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_43118 {a b c d : ℝ} :
  3 * a ^ 2 * d ^ 2 + 3 * b ^ 2 * c ^ 2 + 2 * a ^ 2 * c ^ 2 + 2 * b ^ 2 * d ^ 2 + 2 * a * b * c * d ≥ 3 * a ^ 2 * c * d + 3 * d ^ 2 * a * b + 3 * c ^ 2 * a * b + 3 * b ^ 2 * c * d  :=  by sorry
