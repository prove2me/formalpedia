-- Prove2me | Theorems.Thm_lean_workbook_plus_22858
-- name    : lean_workbook_plus_22858
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/ad86fdbc-5a71-48f3-9432-40e5a877a167
-- statement:
--   Prove: For all positive integers $c$ , we can find 2 numbers $a$ and $b$ , $gcd(a,b)=1$ , such that there are infinitely many positive integers $n$ , satisfy $cn+1 \mid a^n-b^n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22858 (c : ℕ) : ∃ a b : ℕ, Nat.Coprime a b ∧ ∀ n : ℕ, 0 < n → c*n+1 ∣ a^n-b^n   :=  by sorry
