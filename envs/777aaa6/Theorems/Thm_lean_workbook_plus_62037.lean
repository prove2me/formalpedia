-- Prove2me | Theorems.Thm_lean_workbook_plus_62037
-- name    : lean_workbook_plus_62037
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/72bc6a3b-fa37-4357-b604-71876ac81a41
-- statement:
--   Over $(\mathbb{Z}/5\mathbb{Z})[x]$ we have that $p(x)=(x^2+2)^n$ , and since $\mathbb{Z}/5\mathbb{Z}[x]$ is a UFD (because $\mathbb{Z}/5\mathbb{Z}$ is a field), we have that $r(x)=(x^2+2)^a$ , $s(x)=(x^2+2)^b$ for some $a,b\geq 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62037 (n : ℕ) (p r s : Polynomial (ZMod 5)) (hp : p = (X ^ 2 + 2) ^ n) (hr : r = (X ^ 2 + 2) ^ a) (hs : s = (X ^ 2 + 2) ^ b) (hab : a + b = n) : ∃ a b : ℕ, a + b = n ∧ r = (X ^ 2 + 2) ^ a ∧ s = (X ^ 2 + 2) ^ b   :=  by sorry
