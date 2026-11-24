-- Prove2me | Theorems.Thm_syracuse_survivor_descent_outside_mixed_prefix_certificates
-- name    : syracuse_survivor_descent_outside_mixed_prefix_certificates
-- status  : Open
-- author  : @immiq
-- created : 2026-11-24T17:38:55.547433+00:00
-- url     : https://prove2.me/theorems/cfd3cec3-f964-4ae6-8673-04023262638a
-- title:
--   Remaining first-run survivors outside the mixed valuation prefix certificates
-- statement:
--   Retain the previous first-run survivor hypotheses. Let $y$ be the endpoint of the first run and $n$ the original starting value. Suppose no positive word that starts with a single halving and includes a count of at least three provides the simultaneous affine congruence and strict upper bound of the mixed valuation certificate. Show that some iterate from $y$ is below $n$.
-- source:
--   Open complement of the mixed valuation certificate within https://prove2.me/theorems/e81a1897-37e7-4aca-8cd1-fc0dd1b975ac.

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_survivor_descent_outside_mixed_prefix_certificates (k q : ℕ)
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
      (3^k*q) % p = (1+2^s) % p ∧ 2+2*(3^d*u) < 2^k*q))
    (hnomixed : ¬(∃ w : List ℕ, w.head? = some 1 ∧ (∃ a ∈ w, 3 ≤ a) ∧
      (∀ a : ℕ, a ∈ w → 0 < a) ∧
      let y := ordCompl[2] (3^k*q-1)
      let B := 3^w.length*y+syracuseAffineConstant w
      B % 2^(w.sum+1) = 2^w.sum ∧ B < 2^w.sum*(2^k*q-1))) :
    ∃ t : ℕ, syracuseStep^[t] (ordCompl[2] (3^k*q-1)) < 2^k*q-1 := by sorry
