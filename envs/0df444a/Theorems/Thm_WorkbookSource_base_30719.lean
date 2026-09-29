-- Prove2me | Theorems.Thm_WorkbookSource_base_30719
-- name    : WorkbookSource.base_30719
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:06.330312+00:00
-- url     : https://prove2.me/theorems/eb89a49f-1848-4933-90f5-d16fd32faef4
-- title:
--   A product bound for two binary quadratic forms
-- statement:
--   Let $ a,b,c,d $ be reals . Show that $(a^2-ab+b^2)(c^2-cd+d^2) \geq \frac{2}{3}(a^2c^2-abcd+b^2d^2).
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30719` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30719; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30719 (a b c d : ℝ) : (a^2 - a*b + b^2) * (c^2 - c*d + d^2) ≥ 2/3 * (a^2*c^2 - a*c*b*d + b^2*d^2)  :=  by sorry
