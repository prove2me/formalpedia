-- Prove2me | Theorems.Thm_BookSixth_latin_bounds
-- name    : BookSixth.latin_bounds
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-13T01:36:54.41203+00:00
-- url     : https://prove2.me/theorems/c6076667-303d-403a-a2bc-f424ec04ff08
-- title:
--   Chapter 37, Theorem 2: Latin square count
-- statement:
--   For positive n, the number L(n) of labeled Latin squares on a fixed n-symbol alphabet is between (n!)^(2n)/n^(n²) and the product from k=1 to n of (k!)^(n/k). The latter exponents are real.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, Theorem 2: Latin square count, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.latin_bounds (n : ℕ) (hn : 0 < n) :
    ((n.factorial : ℝ) ^ (2*n) / (n : ℝ) ^ (n*n) ≤ latinCount n) ∧
      ((latinCount n : ℝ) ≤ ∏ k ∈ Finset.Icc 1 n,
        (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ))) := by sorry
