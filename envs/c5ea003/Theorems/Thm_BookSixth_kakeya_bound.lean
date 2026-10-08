-- Prove2me | Theorems.Thm_BookSixth_kakeya_bound
-- name    : BookSixth.kakeya_bound
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-13T01:36:53.802748+00:00
-- url     : https://prove2.me/theorems/bb0d49eb-72d5-4cfc-a0dd-72e610963b59
-- title:
--   Chapter 35, Theorem: finite Kakeya lower bound
-- statement:
--   For a finite field F of size q and positive dimension n, a set containing an affine line in every nonzero direction has size at least binomial(q+n−1,n), and therefore at least q^n/n!. The second bound is written without division.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 35, Theorem: finite Kakeya lower bound, p. 250. https://doi.org/10.1007/978-3-662-57265-8_35

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.kakeya_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (hn : 0 < n) (K : Finset (Fin n → F)) (hK : Kakeya K) :
    Nat.choose (Fintype.card F + n - 1) n ≤ K.card ∧
      Fintype.card F ^ n ≤ n.factorial * K.card := by sorry
