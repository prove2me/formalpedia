-- Prove2me | Theorems.Thm_gpy_goodPair_coord_eq_one
-- name    : gpy_goodPair_coord_eq_one
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T01:08:44.100612+00:00
-- url     : https://prove2.me/theorems/f08180d6-f5f0-453a-acc4-88797d67a4a3
-- title:
--   A good pair has trivial i-th coordinates
-- statement:
--   If a support pair $(d,e)$ is good at a coordinate $i$, then $d_i = e_i = 1$. This is forced, not assumed: the $i$-th coordinate modulus divides both the witness shift $w + h_i$ and the combined modulus $L$, hence divides their gcd, which is $1$ by goodness, hence equals $1$, forcing both coordinates to be $1$. This holds unconditionally and is the formal shadow of the classical fact that a prime $n + h_i$ has no divisor strictly between $1$ and itself. Formalization Note: goodness is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY first-moment comparison, formalized from Mathlib (compatible pairs, good pairs, and the singular sum)

import Mathlib
open Classical

theorem gpy_goodPair_coord_eq_one {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    (hg : ∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) :
    d i = 1 ∧ e i = 1 := by sorry
