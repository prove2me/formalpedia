-- Prove2me | Theorems.Thm_lean_workbook_plus_12271
-- name    : lean_workbook_plus_12271
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/55e6828f-b98a-4dec-88d4-c728ff75b8a9
-- statement:
--   First term, $a$ $=$ $13$ . Last term, $L$ $=$ $73$ . Common difference $d$ $=$ $3$ Therefore, number of terms $n$ will be equal to $(($ $L$ - $a$ $)$ $/$ $d)$ $+$ $1$ . Hence, $((73 - 13)/3)$ $+$ $1$ $=$ $20$ $+$ $1$ $=$ $21$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12271  (a L d n : ℕ)
  (h₀ : a = 13)
  (h₁ : L = 73)
  (h₂ : d = 3)
  (h₃ : n = (L - a) / d + 1) :
  n = 21   :=  by sorry
