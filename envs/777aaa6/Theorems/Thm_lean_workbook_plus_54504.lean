-- Prove2me | Theorems.Thm_lean_workbook_plus_54504
-- name    : lean_workbook_plus_54504
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/4aef9638-49c4-4ac8-8825-6bb0be0fcc48
-- statement:
--   If $k\equiv 0\implies k^k\equiv 0\pmod{10}$\nIf $k\equiv 1\implies k^k\equiv 1\pmod{10}$\nIf $k\equiv 2\pmod{10}$ and $k\equiv 0\pmod{4}$ , then $k^k\equiv 6\pmod{10}$\nIf $k\equiv 2\pmod{10}$ and $k\equiv 2\pmod{4}$ , then $k^k\equiv 4\pmod{10}$\nIf $k\equiv 3\pmod{10}$ and $k\equiv 1\pmod{4}$ , then $k^k\equiv 3\pmod{10}$\nIf $k\equiv 3\pmod{10}$ and $k\equiv 3\pmod{4}$ , then $k^k\equiv 7\pmod{10}$\nIf $k\equiv 4\pmod{10}$ and $k\equiv 0\pmod{4}$ , then $k^k\equiv 4\pmod{10}$\nIf $k\equiv 4\pmod{10}$ and $k\equiv 2\pmod{4}$ , then $k^k\equiv 6\pmod{10}$\nIf $k\equiv 5\pmod{10}$ , then $k^k\equiv 5\pmod{10}$\nIf $k\equiv 6\pmod{10}$ , then $k^k\equiv 6\pmod{10}$\nIf $k\equiv 7\pmod{10}$ , and $k\equiv 1\pmod{4}$ , then $k^k\equiv 7\pmod{10}$\nIf $k\equiv 7\pmod{10}$ and $k\equiv 3\pmod{4}$ , then $k^k\equiv 3\pmod{10}$\nIf $k\equiv 8\pmod{10}$ and $k\equiv 0\pmod{4}$ , then $k^k\equiv 6\pmod{10}$\nIf $k\equiv 8\pmod{10}$ and $k\equiv 2\pmod{4}$ , then $k^k\equiv 4\pmod{10}$\nIf $k\equiv 9\pmod{10}$ and $k\equiv 1\pmod{4}$ , then $k^k\equiv 9\pmod{10}$\nIf $k\equiv 9\pmod{10}$ and $k\equiv 3\pmod{4}$ , then $k^k\equiv 3\pmod{10}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54504 :
  ∀ k : ℕ, (k ≡ 0 [ZMOD 10] ∧ k ≡ 0 [ZMOD 4] ∨ k ≡ 1 [ZMOD 10] ∨ k ≡ 2 [ZMOD 10] ∧ k ≡ 0 [ZMOD 4] ∨ k ≡ 2 [ZMOD 10] ∧ k ≡ 2 [ZMOD 4] ∨ k ≡ 3 [ZMOD 10] ∧ k ≡ 1 [ZMOD 4] ∨ k ≡ 3 [ZMOD 10] ∧ k ≡ 3 [ZMOD 4] ∨ k ≡ 4 [ZMOD 10] ∧ k ≡ 0 [ZMOD 4] ∨ k ≡ 4 [ZMOD 10] ∧ k ≡ 2 [ZMOD 4] ∨ k ≡ 5 [ZMOD 10] ∨ k ≡ 6 [ZMOD 10] ∨ k ≡ 7 [ZMOD 10] ∧ k ≡ 1 [ZMOD 4] ∨ k ≡ 7 [ZMOD 10] ∧ k ≡ 3 [ZMOD 4] ∨ k ≡ 8 [ZMOD 10] ∧ k ≡ 0 [ZMOD 4] ∨ k ≡ 8 [ZMOD 10] ∧ k ≡ 2 [ZMOD 4] ∨ k ≡ 9 [ZMOD 10] ∧ k ≡ 1 [ZMOD 4] ∨ k ≡ 9 [ZMOD 10] ∧ k ≡ 3 [ZMOD 4]) → (k^k ≡ 0 [ZMOD 10] ∨ k^k ≡ 1 [ZMOD 10] ∨ k^k ≡ 2 [ZMOD 10] ∨ k^k ≡ 3 [ZMOD 10] ∨ k^k ≡ 4 [ZMOD 10] ∨ k^k ≡ 5 [ZMOD 10] ∨ k^k ≡ 6 [ZMOD 10] ∨ k^k ≡ 7 [ZMOD 10] ∨ k^k ≡ 8 [ZMOD 10] ∨ k^k ≡ 9 [ZMOD 10])   :=  by sorry
