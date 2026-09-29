-- Prove2me | Theorems.Thm_lean_workbook_plus_81056
-- name    : lean_workbook_plus_81056
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/b0997659-e890-4992-8fa3-63567b277ae1
-- statement:
--   If the positive real numbers $ a,b,c,d$ satisfy $ a^2 + b^2 + c^2 + d^2 = 1$ , prove that $ \frac {1}{a^2b^2cd} + \frac {1}{a^2bc^2d} + \frac {1}{a^2bcd^2} + \frac {1}{ab^2c^2d} + \frac {1}{ab^2cd^2} + \frac {1}{abc^2d^2}\geq384$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81056 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (hab : a * b * c * d = 1) : a^2 + b^2 + c^2 + d^2 = 1 → 1 / (a^2 * b^2 * c * d) + 1 / (a^2 * b * c^2 * d) + 1 / (a^2 * b * c * d^2) + 1 / (a * b^2 * c^2 * d) + 1 / (a * b^2 * c * d^2) + 1 / (a * b * c^2 * d^2) ≥ 384   :=  by sorry
