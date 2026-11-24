-- Prove2me | Theorems.Thm_syracuse_fifteen_descent_after_initial_run
-- name    : syracuse_fifteen_descent_after_initial_run
-- status  : Open
-- author  : @immiq
-- created : 2026-11-24T11:40:18.949217+00:00
-- url     : https://prove2.me/theorems/747e0b8d-0cf3-4a0f-8330-b1f862f5898f
-- title:
--   Descent after the first Syracuse run that ends at or above its start
-- statement:
--   Let $k\ge4$, let $q$ be positive and odd, and put $n=2^kq-1$ and $y=\operatorname{oddpart}(3^kq-1)$. In the case $y\ge n$, prove that some Syracuse iterate of $y$ falls strictly below $n$. The absolute target remains the original starting value $n$.
-- source:
--   Residual case in https://prove2.me/theorems/8c399870-0530-4747-94e9-5fb0717268d6 after exactly evaluating the initial ascent.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_fifteen_descent_after_initial_run (k q : ℕ)
    (hk : 4 ≤ k) (hq : 0 < q) (hodd : ¬2 ∣ q)
    (hsurvives : 2^k*q-1 ≤ ordCompl[2] (3^k*q-1)) :
    ∃ t : ℕ, syracuseStep^[t] (ordCompl[2] (3^k*q-1)) < 2^k*q-1 := by sorry
