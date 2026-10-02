-- Prove2me | Theorems.Thm_BookSixth_latin_upper_telescope
-- name    : BookSixth.latin_upper_telescope
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T02:24:19.018274+00:00
-- url     : https://prove2.me/theorems/078b70ea-25d5-4310-adf4-abcc1642d469
-- title:
--   Chapter 37 adapter: row-extension upper bounds telescope to the counting upper bound
-- statement:
--   If per-row extension counts are bounded above by (k!)^(n/k), their product is at most the product of those factors.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.latin_upper_telescope (n : ℕ) (e : ℕ → ℝ) (hnn : ∀ k ∈ Finset.Icc 1 n, 0 ≤ e k) (hstep : ∀ k ∈ Finset.Icc 1 n, e k ≤ (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ))) : ∏ k ∈ Finset.Icc 1 n, e k ≤ ∏ k ∈ Finset.Icc 1 n, (k.factorial : ℝ) ^ ((n : ℝ) / (k : ℝ)) := by sorry
