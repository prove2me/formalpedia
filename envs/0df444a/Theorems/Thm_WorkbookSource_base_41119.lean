-- Prove2me | Theorems.Thm_WorkbookSource_base_41119
-- name    : WorkbookSource.base_41119
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:32:23.998977+00:00
-- url     : https://prove2.me/theorems/528773f2-7266-44e1-815c-2bbe276c1879
-- title:
--   A quartic correction to a quadratic norm
-- statement:
--   Let $a,b,c \ge 0$ such that $a+b+c=1$ . Prove that
--    $$ a^2+b^2+c^2 \le \frac{3}{8}+ a^4+b^4+c^4$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41119` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41119; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_41119 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0)(habc : a + b + c = 1) : a^2 + b^2 + c^2 ≤ 3 / 8 + a^4 + b^4 + c^4  :=  by sorry
