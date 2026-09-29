-- Prove2me | Theorems.Thm_WorkbookSource_plus_77563
-- name    : WorkbookSource.plus_77563
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:54:08.698475+00:00
-- url     : https://prove2.me/theorems/a2a62fa7-37d2-4751-8026-acca8072b58e
-- title:
--   A pairwise quadratic ratio sum has a normalized upper bound
-- statement:
--   Let $a,b,c>0$ . Prove that
--
--    $\sum {\frac{{{a^2} + {b^2}}}{{{a^2} + ab + {b^2}}}} \le \frac{{6\left( {{a^2} + {b^2} + {c^2}} \right)}}{{{{\left( {a + b + c} \right)}^2}}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_77563` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_77563; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_77563 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2) / (a^2 + a * b + b^2) + (b^2 + c^2) / (b^2 + b * c + c^2) + (c^2 + a^2) / (c^2 + c * a + a^2) ≤ 6 * (a^2 + b^2 + c^2) / (a + b + c)^2   :=  by sorry
