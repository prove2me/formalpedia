-- Prove2me | Theorems.Thm_syracuse_survivor_descent_outside_two_step_word_progressions
-- name    : syracuse_survivor_descent_outside_two_step_word_progressions
-- status  : Open
-- author  : @immiq
-- created : 2026-11-25T00:37:21.200707+00:00
-- url     : https://prove2.me/theorems/f0217e0d-bf84-4f06-b0af-71b02deaca9f
-- title:
--   Remaining first-run survivors outside mixed two-step progression certificates
-- statement:
--   Keep the previous first-run survivor assumptions and let $y$ be the endpoint and $n$ the original start. Exclude the following kind of two-step certificate. For distinct positive exact counts $a,b$ with $a\ge2$, let $P=2^{a+b+1}$ and $r=y\bmod P$. The counts at the representative $r$ are $[a,b]$, and $T^2(r)+18\lfloor y/P\rfloor<n$. Show that the remaining starts eventually fall below $n$.
-- source:
--   Open complement after applying the two-step case of the affine progression theorem within https://prove2.me/theorems/cfd3cec3-f964-4ae6-8673-04023262638a.

import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_survivor_descent_outside_two_step_word_progressions (k q : ℕ)
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
      B % 2^(w.sum+1) = 2^w.sum ∧ B < 2^w.sum*(2^k*q-1)))
    (hnoprogression : ¬(∃ a b : ℕ, 2 ≤ a ∧ 0 < b ∧ a ≠ b ∧
      let y := ordCompl[2] (3^k*q-1)
      let P := 2^(a+b+1)
      let r := y%P
      List.ofFn (fun i : Fin 2 => (3*syracuseStep^[i.val] r+1).factorization 2) = [a,b] ∧
      syracuseStep^[2] r + 18*(y/P) < 2^k*q-1)) :
    ∃ t : ℕ, syracuseStep^[t] (ordCompl[2] (3^k*q-1)) < 2^k*q-1 := by sorry
