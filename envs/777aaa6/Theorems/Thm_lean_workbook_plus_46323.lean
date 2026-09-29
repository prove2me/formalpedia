-- Prove2me | Theorems.Thm_lean_workbook_plus_46323
-- name    : lean_workbook_plus_46323
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/0125f4fa-a304-46e1-9f15-fab5d0b89e41
-- statement:
--   Prove that, for a positive integer $n$ and any integer $a$ , $gcd(a,a+n)$ divides $n$ ; hence $gcd(a,a+1)=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46323 (n a : ℤ) (hn : n > 0) : gcd a (a + n) ∣ n   :=  by sorry
