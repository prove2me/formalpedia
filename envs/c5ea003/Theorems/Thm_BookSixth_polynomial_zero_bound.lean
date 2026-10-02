-- Prove2me | Theorems.Thm_BookSixth_polynomial_zero_bound
-- name    : BookSixth.polynomial_zero_bound
-- status  : Proved
-- author  : @xiangyazi24
-- created : 2026-09-13T01:36:46.520465+00:00
-- url     : https://prove2.me/theorems/af8fc9c2-e763-4ed9-87c6-a53db712d6a8
-- title:
--   Chapter 35, Lemma 1: polynomial zeros
-- statement:
--   Over a finite field of size q, a nonzero polynomial in a positive number n of variables has at most d q^(n−1) zeros, where d is its total degree.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 35, Lemma 1: polynomial zeros, p. 249. https://doi.org/10.1007/978-3-662-57265-8_35

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.polynomial_zero_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n : ℕ} (hn : 0 < n) (p : MvPolynomial (Fin n) F) (hp : p ≠ 0) :
    (Finset.univ.filter (fun x : Fin n → F => MvPolynomial.eval x p = 0)).card ≤
      p.totalDegree * Fintype.card F ^ (n-1) := by sorry
