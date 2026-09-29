-- Prove2me | Theorems.Thm_lean_workbook_plus_49909
-- name    : lean_workbook_plus_49909
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/5c378275-9bc4-4fb4-abed-61e3281e1a07
-- statement:
--   if $p\nmid n$ ,then $\mathrm{lcm}(n,n+p)=n(n+p)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49909 (p n : ℕ) (hp : Nat.Prime p) (h : ¬ p ∣ n) : Nat.lcm n (n + p) = n * (n + p)   :=  by sorry
