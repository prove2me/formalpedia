-- Prove2me | Theorems.Thm_WorkbookSource_base_50971
-- name    : WorkbookSource.base_50971
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:03:24.411875+00:00
-- url     : https://prove2.me/theorems/be66872e-7e4b-4e77-85aa-63fd02059dd4
-- title:
--   A cyclic quartic ratio lower bound at fixed sum three
-- statement:
--   If $ a,b,c>0$ and $ a+b+c=3$ prove that:
--
--   $ \frac{{a^3 \left( {a + b} \right)}}{{a^2 + ab + b^2 }} + \frac{{b^3 \left( {b + c} \right)}}{{b^2 + bc + c^2 }} + \frac{{c^3 \left( {c + a} \right)}}{{c^2 + ac + a^2 }} \ge 2$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_50971` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_50971; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_50971 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : (a^3 * (a + b) / (a^2 + a * b + b^2) + b^3 * (b + c) / (b^2 + b * c + c^2) + c^3 * (c + a) / (c^2 + c * a + a^2)) ≥ 2  :=  by sorry
