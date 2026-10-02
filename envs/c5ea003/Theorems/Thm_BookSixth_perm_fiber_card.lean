-- Prove2me | Theorems.Thm_BookSixth_perm_fiber_card
-- name    : BookSixth.perm_fiber_card
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T09:13:20.761993+00:00
-- url     : https://prove2.me/theorems/69d6d2b0-ce9a-4dab-80ac-9017da628f28
-- title:
--   Chapter 37 adapter: permutations fixing one value count
-- statement:
--   The permutations sending i to c are (n-1)! in number.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, adapter lemma for the entropy proof of the Bregman-Minc bound. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.perm_fiber_card (n : Nat) (hn : 0 < n) (i c : Fin n) :
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin n) => σ i = c)).card = (n - 1).factorial := by sorry
