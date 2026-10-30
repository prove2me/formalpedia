-- Prove2me | Theorems.Thm_gpy_goodPair_lcm_i_eq_one
-- name    : gpy_goodPair_lcm_i_eq_one
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T02:51:41.48+00:00
-- url     : https://prove2.me/theorems/1fd834a1-803e-4f41-ac3c-fa1dad34eb49
-- title:
--   A good pair has trivial i-th coordinate lcm
-- statement:
--   For squarefree products, if a pair (d, e) is good at a coordinate i, then lcm (d i) (e i) = 1. Formalization Note: goodness is written out in Mathlib terms, with no local definitions.
-- source:
--   GPY good-count local evaluation, formalized from Mathlib (prime factorization of the good-pair condition)

import Mathlib
open Classical

theorem gpy_goodPair_lcm_i_eq_one {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    (hsqd : Squarefree (∏ j, d j)) (hsqe : Squarefree (∏ j, e j))
    (hgood : ∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) : Nat.lcm (d i) (e i) = 1 := by sorry
