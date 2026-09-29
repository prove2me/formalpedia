-- Prove2me | Theorems.Thm_WorkbookSource_plus_7645
-- name    : WorkbookSource.plus_7645
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T14:44:41.110221+00:00
-- url     : https://prove2.me/theorems/f6d32d12-82ec-45d6-af87-7b3df07039a3
-- title:
--   The complete divisor set of a semiprime
-- statement:
--   Find the divisors of the number $n$ when $n=pq$ and $p, q$ are distinct primes.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_7645` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_7645; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_7645 (n : ℕ) (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hn : n = p*q) : {d | d ∣ n} = {1, p, q, p*q}   :=  by sorry
