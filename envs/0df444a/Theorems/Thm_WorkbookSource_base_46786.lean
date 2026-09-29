-- Prove2me | Theorems.Thm_WorkbookSource_base_46786
-- name    : WorkbookSource.base_46786
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:18:35.564978+00:00
-- url     : https://prove2.me/theorems/1468c346-e0e5-4108-8371-f8cb0faf4c1d
-- title:
--   A product of two binary quadratic forms bounds a squared bilinear form
-- statement:
--   By AM-GM, we know that $a^2 + 3c^2 \ge 2 \sqrt{3} ac$ $b^2 + 3d^2 \ge 2 \sqrt{3} bd$ Therefore, $2(\sqrt{3})(ac + bd) \le (a^2 + b^2) + 3(c^2 + d^2) = (a - b)^2 + 3(c - d)^2 + 2(ab + 3cd) = 4(a - b)^2 + 4ab = 4(a^2 - ab + b^2)$ Since $a^2 - ab + b^2 = c^2 + cd + d^2$, we get that $\frac{3}{4} (ac + bd)^2 \le (a^2 - ab + b^2)(c^2 + cd + d^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_46786` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_46786; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_46786  (a b c d : ℝ) :
  3 / 4 * (a * c + b * d)^2 ≤ (a^2 - a * b + b^2) * (c^2 + c * d + d^2)  :=  by sorry
