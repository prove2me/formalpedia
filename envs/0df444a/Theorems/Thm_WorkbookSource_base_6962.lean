-- Prove2me | Theorems.Thm_WorkbookSource_base_6962
-- name    : WorkbookSource.base_6962
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:25:30.598276+00:00
-- url     : https://prove2.me/theorems/7e74cd1f-2c16-4917-abd5-f70291da1247
-- title:
--   A normalized cubic sum with a pairwise quadratic correction
-- statement:
--   Let a,b,c>0 Prove that:
--    $ \frac {{a^3 + b^3 + c^3 }}{{abc}} + 9\frac {{ab + bc + ac}}{{a^2 + b^2 + c^2 }} \geq 12$
--   I know it's easy but It is nice.
--   It's must be like this:
--    $ \frac {{a^3 + b^3 + c^3 }}{{abc}} + 9\frac {{ab + bc + ac}}{{a^2 + b^2 + c^2 }} \geq 12$
--    $ LHS - RHS = (\sum a^2 - \sum ab)(\sum \frac {1}{ab} - \frac {9}{\sum ab})\geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6962` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6962; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6962 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + b^3 + c^3) / (a * b * c) + 9 * (a * b + b * c + c * a) / (a^2 + b^2 + c^2) ≥ 12  :=  by sorry
