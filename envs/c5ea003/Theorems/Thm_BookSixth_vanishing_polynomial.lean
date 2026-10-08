-- Prove2me | Theorems.Thm_BookSixth_vanishing_polynomial
-- name    : BookSixth.vanishing_polynomial
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-13T01:36:44.857685+00:00
-- url     : https://prove2.me/theorems/fa2f5046-dc33-4fa8-9ead-3082981a4c26
-- title:
--   Chapter 35, Lemma 2: vanishing polynomial
-- statement:
--   If fewer than binomial(n+d,d) points are prescribed in finite affine n-space, a nonzero polynomial of total degree at most d vanishes on all of them.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 35, Lemma 2: vanishing polynomial, p. 249. https://doi.org/10.1007/978-3-662-57265-8_35

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.vanishing_polynomial {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n d : ℕ} (E : Finset (Fin n → F)) (hE : E.card < Nat.choose (n+d) d) :
    ∃ p : MvPolynomial (Fin n) F, p ≠ 0 ∧ p.totalDegree ≤ d ∧
      ∀ x ∈ E, MvPolynomial.eval x p = 0 := by sorry
