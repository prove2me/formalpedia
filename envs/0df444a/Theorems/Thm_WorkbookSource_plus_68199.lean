-- Prove2me | Theorems.Thm_WorkbookSource_plus_68199
-- name    : WorkbookSource.plus_68199
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:44:00.955934+00:00
-- url     : https://prove2.me/theorems/032f3d38-9c6e-429f-b6a8-59f48af46129
-- title:
--   A symmetric sixth-degree polynomial is nonnegative
-- statement:
--   Prove that for positive reals $a$ , $b$ , $c$ : $8 a^6 + 20 a^5 b + 17 a^4 b^2 + 10 a^3 b^3 + 17 a^2 b^4 + 20 a b^5 + 8 b^6 + 20 a^5 c + 18 a^4 b c - 38 a^3 b^2 c - 38 a^2 b^3 c + 18 a b^4 c + 20 b^5 c + 17 a^4 c^2 - 38 a^3 b c^2 - 102 a^2 b^2 c^2 - 38 a b^3 c^2 + 17 b^4 c^2 + 10 a^3 c^3 - 38 a^2 b c^3 - 38 a b^2 c^3 + 10 b^3 c^3 + 17 a^2 c^4 + 18 a b c^4 + 17 b^2 c^4 + 20 a c^5 + 20 b c^5 + 8 c^6 \ge 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_68199` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_68199; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_68199 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 8 * a ^ 6 + 20 * a ^ 5 * b + 17 * a ^ 4 * b ^ 2 + 10 * a ^ 3 * b ^ 3 + 17 * a ^ 2 * b ^ 4 + 20 * a * b ^ 5 + 8 * b ^ 6 + 20 * a ^ 5 * c + 18 * a ^ 4 * b * c - 38 * a ^ 3 * b ^ 2 * c - 38 * a ^ 2 * b ^ 3 * c + 18 * a * b ^ 4 * c + 20 * b ^ 5 * c + 17 * a ^ 4 * c ^ 2 - 38 * a ^ 3 * b * c ^ 2 - 102 * a ^ 2 * b ^ 2 * c ^ 2 - 38 * a * b ^ 3 * c ^ 2 + 17 * b ^ 4 * c ^ 2 + 10 * a ^ 3 * c ^ 3 - 38 * a ^ 2 * b * c ^ 3 - 38 * a * b ^ 2 * c ^ 3 + 10 * b ^ 3 * c ^ 3 + 17 * a ^ 2 * c ^ 4 + 18 * a * b * c ^ 4 + 17 * b ^ 2 * c ^ 4 + 20 * a * c ^ 5 + 20 * b * c ^ 5 + 8 * c ^ 6 ≥ 0   :=  by sorry
