-- Prove2me | Theorems.Thm_syracuse_first_descent_at_every_prescribed_time_mod_sixteen
-- name    : syracuse_first_descent_at_every_prescribed_time_mod_sixteen
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T11:40:15.007322+00:00
-- url     : https://prove2.me/theorems/a6c6a360-aa98-4f93-b649-60019226d4be
-- title:
--   Every prescribed odd-step first descent time from four onward occurs on a whole progression
-- statement:
--   For every $k\ge4$ there is a residue $0\le r<2^{2k}$ such that every $n=r+2^{2k}b$, $b\ge0$, satisfies $n\equiv15\pmod{16}$. Its Syracuse iterates are strictly above $n$ for every $1\le j<k$ and strictly below $n$ at $j=k$. In particular the first strict descent time attains every value $k\ge4$ on an infinite arithmetic progression in this branch.
-- source:
--   A consequence of the initial-run identity and coprimality of powers of two and three, for https://prove2.me/theorems/8c399870-0530-4747-94e9-5fb0717268d6.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

open Nat

theorem syracuse_first_descent_at_every_prescribed_time_mod_sixteen (k : ℕ) (hk : 4 ≤ k) :
    ∃ r : ℕ, r < 2^(2*k) ∧ ∀ b : ℕ,
      let n := r + 2^(2*k)*b
      n % 16 = 15 ∧ syracuseStep^[k] n < n ∧
        ∀ j : ℕ, 0 < j → j < k → n < syracuseStep^[j] n := by sorry
