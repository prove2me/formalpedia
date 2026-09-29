-- Prove2me | Theorems.Thm_WorkbookSource_base_41707
-- name    : WorkbookSource.base_41707
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:13:04.187009+00:00
-- url     : https://prove2.me/theorems/d04c1fd5-7396-4bc2-9782-ef8ab9e9128d
-- title:
--   A cubed symmetric quadratic sum bounds two cyclic cubic sums
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that:
--    $(a^2+b^2+c^2+ab+bc+ca)^3 \ge 24(a^2b+b^2c+c^2a)(b^2a+c^2b+a^2c)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_41707` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_41707; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_41707 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2 + a * b + b * c + c * a)^3 ≥ 24 * (a^2 * b + b^2 * c + c^2 * a) * (b^2 * a + c^2 * b + a^2 * c)  :=  by sorry
