-- Prove2me | Theorems.Thm_BookSixth_standard_pair_relabel_lt
-- name    : BookSixth.standard_pair_relabel_lt
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-25T08:19:08.134367+00:00
-- url     : https://prove2.me/theorems/6c832f20-1270-4cea-a6e9-b32e7f102524
-- title:
--   Piecewise relabeling of two ordered standard circles
-- statement:
--   If $i<j$, the separated unit circles centered at coordinates $3i$ and $3j$ can be carried to `standardCircle 0` and `standardCircle 1` by one continuous ambient-isotopy path.
--
--   The first-coordinate path is a monotone, time-dependent piecewise-linear homeomorphism. It translates the left unit-circle center from $3i$ to $0$, translates the right unit-circle center from $3j$ to $3$, and linearly compresses only the intervening gap. The other two coordinates are unchanged, so the path starts at the identity and the two unit circles remain unit circles. At time one the two selected circles are exactly the first two standard circles.
--
--   This is the ordered geometric adapter used when extracting a pair from a larger unlink certificate. The former affine description was not faithful because a one-dimensional affine scaling would change the radius of a unit circle when the centers are not adjacent.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 15, Theorem 1, p. 100. Corrected source-faithful ordered finite pair relabeling: a monotone piecewise-linear ambient isotopy of the first coordinate, leaving the other two coordinates unchanged. https://doi.org/10.1007/978-3-662-57265-8_15

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.standard_pair_relabel_lt {i j : ℕ} (hij : i < j) :
    ∃ R : ℝ → Space3 ≃ₜ Space3,
      Continuous (fun p : ℝ × Space3 => R p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (R p.1).symm p.2) ∧
      (∀ x, R 0 x = x) ∧
      (R 1) '' standardCircle i = standardCircle 0 ∧
      (R 1) '' standardCircle j = standardCircle 1 := by sorry
