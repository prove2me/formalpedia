-- Prove2me | Theorems.Thm_lean_workbook_plus_29817
-- name    : lean_workbook_plus_29817
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/571b3caf-4fe2-45f1-a3a6-22ad211b3daf
-- statement:
--   Let $c$ be a nonnegative integer, and define $a_n = n^2 + c$ (for $n \geq 1)$ . Define $d_n$ as the greatest common divisor of $a_n$ and $a_{n + 1}$ .\n(a) Suppose that $c = 0$ . Show that $d_n = 1,\ \forall n \geq 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29817 (c : ℕ) (hc : c = 0) (n : ℕ) (hn : n >= 1) : Nat.gcd (n^2 + c) ((n + 1)^2 + c) = 1   :=  by sorry
