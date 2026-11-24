-- Prove2me | Theorems.Thm_syracuse_survivor_descent_outside_two_halving_certificates
-- name    : syracuse_survivor_descent_outside_two_halving_certificates
-- status  : Open
-- author  : @immiq
-- created : 2026-11-24T17:05:22.964517+00:00
-- url     : https://prove2.me/theorems/e81a1897-37e7-4aca-8cd1-fc0dd1b975ac
-- title:
--   Remaining descent outside all certified two-halving blocks
-- statement:
--   Keep the previous first-run survivor conditions and assume there is no pair $(s,d)$ meeting the certified dyadic congruence and integer inequality in the formal statement. Show that the orbit of the first-run endpoint eventually falls below the original start $2^kq-1$.
-- source:
--   Open complement of the two-halving certificates within https://prove2.me/theorems/6cea8336-6355-4143-8aae-9d45bb0f0714.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_survivor_descent_outside_two_halving_certificates (k q : ℕ)
    (hk : 4 ≤ k) (hq : 0 < q) (hodd : ¬2 ∣ q)
    (hsurvives : 2^k*q-1 ≤ ordCompl[2] (3^k*q-1))
    (hmiss : ¬∃ s b : ℕ, 0 < s ∧ 2^(k+s) < (3:ℕ)^k ∧
      2^(k+s+b) ≤ (3:ℕ)^(k+1) ∧ (3:ℕ)^(k+1) < 2^(k+s+b+1) ∧
      2^(s+b+1)+2^s+3 ≤ q ∧
      (3^(k+1)*q+2^s) % 2^(s+b+1) = 3 % 2^(s+b+1))
    (houtside : ¬(6 ≤ k ∧ (3^(k-1)*q) % 4^(2*k+1) = 1))
    (hnocert : ¬(∃ s d : ℕ, 0 < s ∧ 1+2^s < 3^k*q ∧
      let p := 2^(s+1)*4^d
      let u := (3^k*q-(1+2^s))/p
      (3^k*q) % p = (1+2^s) % p ∧ 2+2*(3^d*u) < 2^k*q)) :
    ∃ t : ℕ, syracuseStep^[t] (ordCompl[2] (3^k*q-1)) < 2^k*q-1 := by sorry
