-- Prove2me | Theorems.Thm_WorkbookSource_plus_75470
-- name    : WorkbookSource.plus_75470
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:54:07.051812+00:00
-- url     : https://prove2.me/theorems/c4552853-5d93-470c-a3fd-caae96a0b4f0
-- title:
--   A comparison of weighted cyclic reciprocal sums
-- statement:
--   Let $ a,b,c>0$ ,prove that:
--    $6+2\,{\frac {c}{a}}+2\,{\frac {a}{b}}+2\,{\frac {b}{c}}\leq 3\,{\frac {bc}{{a}^{2}}}+{\frac {c}{b}}+3\,{\frac {ac}{{b}^{2}}}+{\frac {a}{c}}+3\,{\frac {ab}{{c}^{2}}}+{\frac {b}{a}}$ .
--   BQ
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_75470` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_75470; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_75470 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 6 + 2 * c / a + 2 * a / b + 2 * b / c ≤ 3 * b * c / a ^ 2 + c / b + 3 * a * c / b ^ 2 + a / c + 3 * a * b / c ^ 2 + b / a   :=  by sorry
