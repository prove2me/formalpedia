-- Prove2me | Theorems.Thm_lean_workbook_plus_38388
-- name    : lean_workbook_plus_38388
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/b0da608a-1ec0-4ae0-81fd-26d772998154
-- statement:
--   Prove that if $\gcd(x,y)=d>1$, then $d\mid x'$ and $d\mid y'$, where $x=dx'$ and $y=dy'$ with $\gcd(x',y')=1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38388 (x y : ℕ) (h : 1 < Nat.gcd x y) : (Nat.gcd x y) ∣ x ∧ (Nat.gcd x y) ∣ y   :=  by sorry
