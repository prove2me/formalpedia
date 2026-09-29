-- Prove2me | Theorems.Thm_lean_workbook_plus_35790
-- name    : lean_workbook_plus_35790
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/95e35f0e-945d-42c9-ad4e-64629ef475df
-- statement:
--   $lcm(n, m) \cdot lcm(n+1, m+1) = \frac{nm}{gcd(n, m)} \cdot \frac{(n+1)(m+1)}{gcd(n+1, m+1)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35790 : ∀ n m : ℕ, (Nat.lcm n m) * (Nat.lcm (n + 1) (m + 1)) = (n * m / Nat.gcd n m) * ((n + 1) * (m + 1) / Nat.gcd (n + 1) (m + 1))   :=  by sorry
