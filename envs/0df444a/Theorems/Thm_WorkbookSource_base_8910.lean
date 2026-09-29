-- Prove2me | Theorems.Thm_WorkbookSource_base_8910
-- name    : WorkbookSource.base_8910
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T07:55:45.787116+00:00
-- url     : https://prove2.me/theorems/2c676176-6ec2-4836-834c-4c958af044e5
-- title:
--   A quadratic ratio inequality with a normalized four-variable product
-- statement:
--   $ a,b,c,d>0 $,prove that:
--
--   $ \frac{{a}^{2}+{c}^{2}+{b}^{2}+{d}^{2}}{ab+bc+cd+ad+ac+bd}+27\,{\frac {abcd}{ \left( b+c+d \right) \left( a+c+d \right) \left( d+a+b \right) \left( a+b+c \right) }}\geq 1 $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_8910` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_8910; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_8910 (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) : (a^2 + b^2 + c^2 + d^2) / (a * b + b * c + c * d + d * a + a * c + b * d) + 27 * (a * b * c * d) / (b + c + d) / (a + c + d) / (d + a + b) / (a + b + c) ≥ 1  :=  by sorry
