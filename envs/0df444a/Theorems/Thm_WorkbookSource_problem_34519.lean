-- Prove2me | Theorems.Thm_WorkbookSource_problem_34519
-- name    : WorkbookSource.problem_34519
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:37:05.995641+00:00
-- url     : https://prove2.me/theorems/b0e09777-99ae-47a6-aa4f-c162c9c6f0ef
-- title:
--   Coprimality with a product
-- statement:
--   Suppose that $\gcd(h, k) = 1$ . Show that for every $a \in \mathbb N$ , we have that
--
--    $$[\gcd(a, h) = 1 \text{\ \ and \ } \gcd(a, k) = 1] \iff \gcd(a, hk) = 1.$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34519` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34519; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.problem_34519 {a h k : ℕ} (h1 : Nat.Coprime h k) :  Nat.Coprime a h ∧ Nat.Coprime a k ↔ Nat.Coprime a (h * k)  :=  by sorry
