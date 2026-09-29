-- Prove2me | Theorems.Thm_lean_workbook_plus_12768
-- name    : lean_workbook_plus_12768
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/2cb37054-9915-4be6-8baa-ceb8309f2f25
-- statement:
--   Let $\sigma(n)$ denote the sum of the divisors of $n$ . Then $f(768) - f(384) = \frac{\sigma(768)}{768} - \frac{\sigma(384)}{384} = \frac{(1+\dots+2^8)(1+3)}{768} - \frac{(1+\dots+2^7)(1+3)}{384} = \frac{511 \cdot 4}{768} - \frac{255 \cdot 4}{384} = \frac{4}{768} = \boxed{\frac{1}{192}}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12768 :
  ((∑ k in (Nat.divisors 768), k) / 768 - (∑ k in (Nat.divisors 384), k) / 384) = 1 / 192   :=  by sorry
