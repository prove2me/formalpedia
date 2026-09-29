-- Prove2me | Theorems.Thm_lean_workbook_plus_78020
-- name    : lean_workbook_plus_78020
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/3bc707a0-9719-4cda-96c3-92e67bc9db52
-- statement:
--   The integers $a, b, c, d$ are all positive, not necessarily distinct. We know that $a + b + c + d = 10$ and $343a +49b +7c +d = 988$ . Find $1000a +100b +10c +d$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78020 (a b c d : ℤ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hd : d > 0) (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (habc : a ≠ b ∧ b ≠ c ∧ c ≠ d) : a + b + c + d = 10 ∧ 343*a + 49*b + 7*c + d = 988 → 1000*a + 100*b + 10*c + d = 2611   :=  by sorry
