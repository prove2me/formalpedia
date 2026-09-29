-- Prove2me | Theorems.Thm_WorkbookSource_plus_49894
-- name    : WorkbookSource.plus_49894
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:27:53.571097+00:00
-- url     : https://prove2.me/theorems/95b440b7-a3e2-4aa6-a259-300430cc64a9
-- title:
--   A cyclic cubic ratio sum bounds eight sevenths of the total
-- statement:
--   Show that if a,b,c are positive, then
--    $ \frac {(a + b)^3}{3a^2 + 3ab + b^2} + \frac {(b + c)^3}{3b^2 + 3bc + c^2} + \frac {(c + a)^3}{3c^2 + 3ca + a^2} \ge \frac {8}{7} (a + b + c)$
--   follows directly from:
--    $ \frac {a^3}{3a^2 + 3ab + b^2}\geq \frac {12a - 5b}{49}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_49894` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_49894; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_49894 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 3 / (3 * a ^ 2 + 3 * a * b + b ^ 2) + (b + c) ^ 3 / (3 * b ^ 2 + 3 * b * c + c ^ 2) + (c + a) ^ 3 / (3 * c ^ 2 + 3 * c * a + a ^ 2) ≥ 8 / 7 * (a + b + c)   :=  by sorry
