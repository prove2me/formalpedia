-- Prove2me | Theorems.Thm_BookSixth_latin_lower_frac_pos
-- name    : BookSixth.latin_lower_frac_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T00:07:26.967157+00:00
-- url     : https://prove2.me/theorems/f246b19c-f331-4ab2-ab6e-dfbe1e17b343
-- title:
--   Chapter 37 adapter: positivity of the lower-bound fraction
-- statement:
--   For positive $n$, the lower-bound fraction $(n!)^{2n}/n^{n^2}$ from Chapter 37, Theorem 2 is strictly positive.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, Theorem 2 lower-bound positivity adapter, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.latin_lower_frac_pos (n : ℕ) (hn : 0 < n) :
    0 < (n.factorial : ℝ) ^ (2*n) / (n : ℝ) ^ (n*n) := by sorry
