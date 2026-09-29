-- Prove2me | Theorems.Thm_lean_workbook_plus_25432
-- name    : lean_workbook_plus_25432
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/f26de1e5-b203-40c2-b198-a1fa70052f21
-- statement:
--   Show that $n^5 \equiv 1$ (mod $a$ ) implies $n^{5m} \equiv 1$ (mod $a$ ) for all whole numbers $m$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25432 (n m a : ℕ) (hn: n^5 ≡ 1 [ZMOD a]) : n^(5*m) ≡ 1 [ZMOD a]   :=  by sorry
