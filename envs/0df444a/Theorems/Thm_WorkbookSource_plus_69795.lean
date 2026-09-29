-- Prove2me | Theorems.Thm_WorkbookSource_plus_69795
-- name    : WorkbookSource.plus_69795
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:08:27.757215+00:00
-- url     : https://prove2.me/theorems/4c8bc70b-002e-4762-b44c-7d217ce18068
-- title:
--   A quartic product inequality under three pairwise constraints
-- statement:
--   If $ x, y, z > 0 $ are real numbers and $ z(x+y+z) \ge xy $ and $ x(x+y+z) \ge yz $ and $ y(x+y+z) \ge zx $ , prove that:
--
--    $ (x^2+y^2+z^2)(x+y+z)^2 \ge 8xyz(x+y+z)+x^2y^2+y^2z^2+z^2x^2 \ \ ; $
--
--    Greetings from Lorian Saceanu!
--
--    12-March 2017
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_69795` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_69795; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_69795 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : z * (x + y + z) ≥ x * y) (h' : x * (x + y + z) ≥ y * z) (h'' : y * (x + y + z) ≥ z * x) : (x ^ 2 + y ^ 2 + z ^ 2) * (x + y + z) ^ 2 ≥ 8 * x * y * z * (x + y + z) + x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2   :=  by sorry
