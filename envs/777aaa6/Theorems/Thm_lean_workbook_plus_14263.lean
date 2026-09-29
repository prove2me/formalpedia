-- Prove2me | Theorems.Thm_lean_workbook_plus_14263
-- name    : lean_workbook_plus_14263
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/4bfe5b45-c43c-45c7-83de-52c7eea91256
-- statement:
--   Given $m|n^a+1$ and $m|n^b+1$, prove that $m$ divides $gcd(n^a+1, n^b+1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14263 {m n a b : ℕ} (hm : m ∣ n^a + 1) (hn : m ∣ n^b + 1) : m ∣ Nat.gcd (n^a + 1) (n^b + 1)   :=  by sorry
