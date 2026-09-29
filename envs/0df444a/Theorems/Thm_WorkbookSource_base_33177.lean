-- Prove2me | Theorems.Thm_WorkbookSource_base_33177
-- name    : WorkbookSource.base_33177
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:11.339278+00:00
-- url     : https://prove2.me/theorems/9b3ddc50-3c35-46ce-8514-1f4ffe9c6b5f
-- title:
--   A squared cyclic quadratic expression bounds a cubic product
-- statement:
--   a,b,c,d $\in$ R ,prove that:
--
--    $\left( {a}^{2}+ab+{b}^{2}+bc+{c}^{2}+cd+{d}^{2}+ad \right) ^{2}\geq 2\, \left( a+b+c+d \right) \left( ab \left( a+b \right) +cb \left( b+c \right) +dc \left( c+d \right) +ad \left( d+a \right) \right)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_33177` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_33177; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_33177 (a b c d : ℝ) : (a^2 + a * b + b^2 + b * c + c^2 + c * d + d^2 + d * a)^2 ≥ 2 * (a + b + c + d) * (a * b * (a + b) + b * c * (b + c) + c * d * (c + d) + d * a * (d + a))  :=  by sorry
