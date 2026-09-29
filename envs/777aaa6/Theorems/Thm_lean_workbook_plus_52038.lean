-- Prove2me | Theorems.Thm_lean_workbook_plus_52038
-- name    : lean_workbook_plus_52038
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/3b085beb-6aa7-4c8c-88e0-317b51ed4d1d
-- statement:
--   Prove that if $a$ and $b$ are relatively prime, then $\phi{(a)}\phi{(b)}=\phi{(ab)}$, where $\phi$ is the Euler's totient function.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52038 (a b : ℕ) (hab : Nat.Coprime a b) : Nat.totient a * Nat.totient b = Nat.totient (a * b)   :=  by sorry
