-- Prove2me | Theorems.Thm_syracuse_survivor_descent_outside_long_contraction_classes
-- name    : syracuse_survivor_descent_outside_long_contraction_classes
-- status  : Open
-- author  : @immiq
-- created : 2026-11-24T12:36:45.096002+00:00
-- url     : https://prove2.me/theorems/6cea8336-6355-4143-8aae-9d45bb0f0714
-- title:
--   Remaining first-run survivors outside the long contraction classes
-- statement:
--   Retain all hypotheses from the previous first-run survivor problem and exclude $k\ge6$ with $3^{k-1}q\equiv1\pmod{4^{2k+1}}$. For the remaining inputs show that some Syracuse iterate of the first-run endpoint falls below the original start $2^kq-1$.
-- source:
--   Open complement after the long-contraction progressions in https://prove2.me/theorems/2608ffdc-2f1d-4f5a-bf8d-7c3af9948d46.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_survivor_descent_outside_long_contraction_classes (k q : ℕ)
    (hk : 4 ≤ k) (hq : 0 < q) (hodd : ¬2 ∣ q)
    (hsurvives : 2^k*q-1 ≤ ordCompl[2] (3^k*q-1))
    (hmiss : ¬∃ s b : ℕ, 0 < s ∧ 2^(k+s) < (3:ℕ)^k ∧
      2^(k+s+b) ≤ (3:ℕ)^(k+1) ∧ (3:ℕ)^(k+1) < 2^(k+s+b+1) ∧
      2^(s+b+1)+2^s+3 ≤ q ∧
      (3^(k+1)*q+2^s) % 2^(s+b+1) = 3 % 2^(s+b+1))
    (houtside : ¬(6 ≤ k ∧ (3^(k-1)*q) % 4^(2*k+1) = 1)) :
    ∃ t : ℕ, syracuseStep^[t] (ordCompl[2] (3^k*q-1)) < 2^k*q-1 := by sorry
