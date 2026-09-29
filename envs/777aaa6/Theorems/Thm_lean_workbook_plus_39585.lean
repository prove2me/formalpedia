-- Prove2me | Theorems.Thm_lean_workbook_plus_39585
-- name    : lean_workbook_plus_39585
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/b19545b5-96bd-49c9-b122-e99f9c0c1078
-- statement:
--   Prove that if $x\equiv a\pmod m$ and $x \equiv a \pmod n$ then $x\equiv a \pmod{mn}$, given that $m$ and $n$ are coprime.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39585 (a m n x : ℕ) (hm : m > 0) (hn : n > 0) (hmn : Nat.Coprime m n) : x ≡ a [ZMOD m] ∧ x ≡ a [ZMOD n] → x ≡ a [ZMOD m * n]   :=  by sorry
