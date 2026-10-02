-- Prove2me | Theorems.Thm_BookSixth_doubly_stochastic_of_regular_smul
-- name    : BookSixth.doubly_stochastic_of_regular_smul
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T01:50:28.019618+00:00
-- url     : https://prove2.me/theorems/fc8b992a-3afe-4ccb-a75e-32c9743cecd1
-- title:
--   Chapter 37 adapter: normalizing regular matrices to doubly stochastic
-- statement:
--   A nonnegative matrix with all row and column sums $c \ne 0$, scaled by $1/c$, is doubly stochastic. The normalization step used to apply van der Waerden in Chapter 37.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, doubly-stochastic normalization adapter, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.doubly_stochastic_of_regular_smul (n : ℕ) (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (hc : c ≠ 0) (hnn : ∀ i j, 0 ≤ M i j)
    (hrow : ∀ i, ∑ j, M i j = c) (hcol : ∀ j, ∑ i, M i j = c) :
    (∀ i j, 0 ≤ (c⁻¹ • M) i j) ∧ (∀ i, ∑ j, (c⁻¹ • M) i j = 1) ∧ (∀ j, ∑ i, (c⁻¹ • M) i j = 1) := by sorry
