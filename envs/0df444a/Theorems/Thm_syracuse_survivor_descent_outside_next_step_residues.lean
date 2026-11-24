-- Prove2me | Theorems.Thm_syracuse_survivor_descent_outside_next_step_residues
-- name    : syracuse_survivor_descent_outside_next_step_residues
-- status  : Open
-- author  : @immiq
-- created : 2026-11-24T12:10:13.565311+00:00
-- url     : https://prove2.me/theorems/2608ffdc-2f1d-4f5a-bf8d-7c3af9948d46
-- title:
--   Remaining first-run survivors outside the next-step descent classes
-- statement:
--   Let $k\ge4$, $q$ be positive and odd, $n=2^kq-1$, and $y=\operatorname{oddpart}(3^kq-1)\ge n$. Suppose $q$ misses every next-step residue satisfying the exact slope and size hypotheses in the Lean statement. Show that some Syracuse iterate of $y$ falls below the original target $n$.
-- source:
--   Open complement of the modular next-step test inside https://prove2.me/theorems/747e0b8d-0cf3-4a0f-8330-b1f862f5898f.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_survivor_descent_outside_next_step_residues (k q : ℕ)
    (hk : 4 ≤ k) (hq : 0 < q) (hodd : ¬2 ∣ q)
    (hsurvives : 2^k*q-1 ≤ ordCompl[2] (3^k*q-1))
    (hmiss : ¬∃ s b : ℕ, 0 < s ∧ 2^(k+s) < (3:ℕ)^k ∧
      2^(k+s+b) ≤ (3:ℕ)^(k+1) ∧ (3:ℕ)^(k+1) < 2^(k+s+b+1) ∧
      2^(s+b+1)+2^s+3 ≤ q ∧
      (3^(k+1)*q+2^s) % 2^(s+b+1) = 3 % 2^(s+b+1)) :
    ∃ t : ℕ, syracuseStep^[t] (ordCompl[2] (3^k*q-1)) < 2^k*q-1 := by sorry
