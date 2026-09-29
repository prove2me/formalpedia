-- Prove2me | Theorems.Thm_lean_workbook_plus_50688
-- name    : lean_workbook_plus_50688
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/cbcf7907-aa7c-44ba-ba9b-55f28d862000
-- statement:
--   Let $g=GCD(a,d)$ and let $a=pg$ and $d=qg$ with $GCD(p,q)=1$ then we have $a_i=a+di=pg+qgi=g\left(p+qi\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50688 {a d g a_i : ℕ} (hg : g = Nat.gcd a d) (ha : a = p * g) (hd : d = q * g) (hpq : Nat.gcd p q = 1) (hii : a_i = a + d * i) : a_i = g * (p + q * i)   :=  by sorry
