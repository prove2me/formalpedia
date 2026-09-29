-- Prove2me | Theorems.Thm_lean_workbook_plus_46457
-- name    : lean_workbook_plus_46457
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/111a3201-6859-463d-8239-343f15eac5ce
-- statement:
--   So $t_n=2^{2^n}$ and $a_n=2^{2^n+1}-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46457 (t a : ℕ → ℕ) (n : ℕ) (ht : t n = 2^(2^n)) (ha : a n = 2^(2^n+1)-1) : a n = 2 * t n - 1   :=  by sorry
