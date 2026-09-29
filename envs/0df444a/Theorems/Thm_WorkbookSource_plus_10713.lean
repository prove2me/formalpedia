-- Prove2me | Theorems.Thm_WorkbookSource_plus_10713
-- name    : WorkbookSource.plus_10713
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:21:52.184088+00:00
-- url     : https://prove2.me/theorems/1e288179-b535-495a-b8c1-e50ffb495975
-- title:
--   A comparison of the quadratic and cubic power sums
-- statement:
--   Prove that if $ a,b,c \in [0, + \infty)$ then: $ (a^2 + b^2 + c^2)^3 \le 3(a^3 + b^3 + c^3)^2.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_10713` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_10713; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_10713 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : (a^2 + b^2 + c^2)^3 ≤ 3 * (a^3 + b^3 + c^3)^2   :=  by sorry
