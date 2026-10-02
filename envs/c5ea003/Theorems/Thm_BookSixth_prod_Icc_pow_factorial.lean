-- Prove2me | Theorems.Thm_BookSixth_prod_Icc_pow_factorial
-- name    : BookSixth.prod_Icc_pow_factorial
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-17T23:29:10.063527+00:00
-- url     : https://prove2.me/theorems/817a85cd-82d6-4122-b9a4-d2e3068e93a8
-- title:
--   Chapter 37 adapter: row-product identity for the lower bound
-- statement:
--   For every $n$, $\prod_{k=1}^n k^n = (n!)^n$. This telescopes the product of the van der Waerden row-extension bounds $j^n \cdot n!/n^n$ into the lower counting bound $(n!)^{2n}/n^{n^2}$ of Chapter 37, Theorem 2.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, Theorem 2 lower-bound product computation, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.prod_Icc_pow_factorial (n : ℕ) :
    ∏ k ∈ Finset.Icc 1 n, (k : ℝ) ^ n = (n.factorial : ℝ) ^ n := by sorry
