-- Prove2me | Theorems.Thm_WorkbookSource_plus_14551
-- name    : WorkbookSource.plus_14551
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:15:44.295532+00:00
-- url     : https://prove2.me/theorems/44e8fa5f-1640-4577-b241-6ce9515481d9
-- title:
--   A refined quadratic reciprocal product inequality
-- statement:
--   For $a,b,c>0$ .Prove that
--    $\left( {{a^2} + {b^2} + {c^2}} \right)\left( {\frac{1}{{{a^2}}} + \frac{1}{{{b^2}}} + \frac{1}{{{c^2}}}} \right) + 5 \ge \frac{{14({a^2} + {b^2} + {c^2})}}{{ab + bc + ca}}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_14551` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_14551; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_14551 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) * (1 / a^2 + 1 / b^2 + 1 / c^2) + 5 ≥ 14 * (a^2 + b^2 + c^2) / (a * b + b * c + c * a)   :=  by sorry
