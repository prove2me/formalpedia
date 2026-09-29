-- Prove2me | Theorems.Thm_lean_workbook_plus_6471
-- name    : lean_workbook_plus_6471
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/e8a337a0-17a1-4c81-b755-f5f614771a10
-- statement:
--   Prove that the $\gcd(a,b)=\gcd(xa,b)$ if $\gcd(x,b)=1\forall a,x,b \in \mathbb{N}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6471 (a b x : ℕ) (hx: Nat.Coprime x b) : Nat.gcd a b = Nat.gcd (x * a) b   :=  by sorry
