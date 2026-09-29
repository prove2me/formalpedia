-- Prove2me | Theorems.Thm_lean_workbook_plus_60300
-- name    : lean_workbook_plus_60300
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/64fb1274-9728-4701-87b6-f0c0c59be932
-- statement:
--   Given $ a, b, c \geq\ 0$ satisfy $ ab + bc + ca = 3$ . Prove that: $ \sqrt [3]{5a^3 + 3a} + \sqrt [3]{5b^3 + 3b} + \sqrt [3]{5c^3 + 3c} \geq\ 6$ . PS: It exitst an easy proof by Am-Gm, my friend
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60300 (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hab : a * b + b * c + c * a = 3) : (5 * a ^ 3 + 3 * a) ^ (1 / 3) + (5 * b ^ 3 + 3 * b) ^ (1 / 3) + (5 * c ^ 3 + 3 * c) ^ (1 / 3) ≥ 6   :=  by sorry
