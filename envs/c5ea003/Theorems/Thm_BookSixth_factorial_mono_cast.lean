-- Prove2me | Theorems.Thm_BookSixth_factorial_mono_cast
-- name    : BookSixth.factorial_mono_cast
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T00:53:18.635736+00:00
-- url     : https://prove2.me/theorems/499c7e38-3588-47cd-9f6b-3ab4c0c1942f
-- title:
--   Chapter 37 adapter: factorial monotonicity over the reals
-- statement:
--   Factorials are monotone, cast to the reals: $n \le m$ implies $(n! : \mathbb{R}) \le (m! : \mathbb{R})$. Supports factor comparisons in the Chapter 37 counting bounds.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, factorial comparison adapter, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.factorial_mono_cast (n m : ℕ) (h : n ≤ m) :
    (n.factorial : ℝ) ≤ (m.factorial : ℝ) := by sorry
