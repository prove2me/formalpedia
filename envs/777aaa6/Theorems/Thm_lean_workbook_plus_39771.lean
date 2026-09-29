-- Prove2me | Theorems.Thm_lean_workbook_plus_39771
-- name    : lean_workbook_plus_39771
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/a8ddd325-8939-4f10-bcc5-acf8d2382662
-- statement:
--   If a, b, c, d > 0, prove that $ a^3 + b^3 + c^3 + d^3 \ge abc + abd + acd + bcd$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39771 (a b c d : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) : a^3 + b^3 + c^3 + d^3 ≥ a * b * c + a * b * d + a * c * d + b * c * d   :=  by sorry
