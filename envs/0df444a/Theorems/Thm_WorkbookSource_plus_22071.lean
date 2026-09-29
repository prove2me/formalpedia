-- Prove2me | Theorems.Thm_WorkbookSource_plus_22071
-- name    : WorkbookSource.plus_22071
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T22:51:18.872784+00:00
-- url     : https://prove2.me/theorems/c2e4e8bf-fc72-4aee-8b1b-d9ac814a4bf2
-- title:
--   A sixth-degree product bound involving a triple product
-- statement:
--   Maybe $8(1+a+a^{2})(1+b+b^{2})(1+c+c^{2})\geq 27 (1+a)(1+b)(1+c)$
--
--   $\Leftrightarrow 8(x^{2}+xy+y^{2})(y^{2}+yz+z^{2})(z^{2}+zx+x^{2})\ge 27(x+y)(y+z)(z+x)xyz$ ?
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_22071` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_22071; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_22071 (x y z : ℝ) : 8 * (x ^ 2 + x * y + y ^ 2) * (y ^ 2 + y * z + z ^ 2) * (z ^ 2 + z * x + x ^ 2) ≥ 27 * (x + y) * (y + z) * (z + x) * x * y * z   :=  by sorry
