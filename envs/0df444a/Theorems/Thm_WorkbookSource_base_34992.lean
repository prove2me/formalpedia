-- Prove2me | Theorems.Thm_WorkbookSource_base_34992
-- name    : WorkbookSource.base_34992
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:11:27.254899+00:00
-- url     : https://prove2.me/theorems/8a8b1545-9605-488d-88de-2bd2c834eacd
-- title:
--   A quartic and squared-sum bound in four variables
-- statement:
--   If $a, b, c, d$ be real and $a^2+b^2+c^2+d^2=4.$ Then $a^4+b^4+c^4+d^4+\frac{4}{3}(a+b+c+d)^2\leq \frac{76}{3}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34992` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34992; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_34992 (a b c d : ℝ) (h : a^2 + b^2 + c^2 + d^2 = 4) :
  a^4 + b^4 + c^4 + d^4 + (4 / 3) * (a + b + c + d)^2 ≤ (76 / 3)  :=  by sorry
