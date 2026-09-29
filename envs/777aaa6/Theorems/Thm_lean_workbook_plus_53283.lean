-- Prove2me | Theorems.Thm_lean_workbook_plus_53283
-- name    : lean_workbook_plus_53283
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/0cc37363-e1f7-43d0-8138-2fa6ed8afccf
-- statement:
--   Let $s(n) = \frac16 n^3 - \frac12 n^2 + \frac13 n$ .\n\n(a) Show that $s(n)$ is an integer whenever $n$ is an integer.\n\n(b) How many integers $n$ with $0 < n \le 2008$ are such that $s(n)$ is divisible by $4$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53283 (n : ℤ) : ∃ k : ℤ, 1/6 * n^3 - 1/2 * n^2 + 1/3 * n = k   :=  by sorry
