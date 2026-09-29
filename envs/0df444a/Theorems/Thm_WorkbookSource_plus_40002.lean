-- Prove2me | Theorems.Thm_WorkbookSource_plus_40002
-- name    : WorkbookSource.plus_40002
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:06:59.274982+00:00
-- url     : https://prove2.me/theorems/7eca2d9a-27d3-441a-85ed-10d52183bebd
-- title:
--   A symmetric quadratic ratio bounds cyclic difference ratios
-- statement:
--   Given $ a, b, c > 0$ . Prove that: $ \frac {a^2 + b^2 + c^2}{ab + bc + ca} \geq\ \frac {a^2 + bc - ca}{a^2 + ab + bc} + \frac {b^2 + ca - ba}{b^2 + bc + ca} + \frac {c^2 + ab - bc}{c^2 + ca + ab}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_40002` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_40002; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_40002 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^2 + b^2 + c^2) / (a * b + b * c + c * a) ≥ (a^2 + b * c - c * a) / (a^2 + a * b + b * c) + (b^2 + c * a - a * b) / (b^2 + b * c + c * a) + (c^2 + a * b - b * c) / (c^2 + c * a + a * b)   :=  by sorry
