-- Prove2me | Theorems.Thm_Heisenberg125_Heis_eq_zero_of_cast_eq_zero
-- name    : Heisenberg125.Heis.eq_zero_of_cast_eq_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:47:06.629539+00:00
-- url     : https://prove2.me/theorems/25bbc4d9-6b72-430d-8965-0c3001e7e4f9
-- title:
--   A natural number `n ≤ p - 1` whose class in `ZMod p` vanishes is zero.
-- statement:
--   A natural number `n ≤ p - 1` whose class in `ZMod p` vanishes is zero.
--
--   ```lean
--   theorem Heisenberg125.Heis.eq_zero_of_cast_eq_zero(hp : 0 < p) {n : ℕ} (hn : n ≤ p - 1)
--       (h : (n : ZMod p) = 0) : n = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/Heisenberg125/LowerBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/Heisenberg125/LowerBound.lean#L46

-- Thm stub generated from Algebra/Heisenberg125/LowerBound.lean
import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_LowerBound
/-
# The lower bound `d(H_{p^3}) ≥ 3p - 3`

The explicit product-one-free sequence is `x^{p-1} y^{p-1} v^{p-1}`, of length
`3p - 3`.  For `p = 5` this gives the lower bound `d(H_125) ≥ 12` of the paper
"The small Davenport constant of the Heisenberg group of order 125".

The proof is a clean application of the product formula `Heis.prod_eq`: the
first two coordinates of a product are order independent, so a product-one
subsequence must use a multiple of `p` copies of `x` and of `y`; as at most
`p - 1` copies of each are available, it uses none, and is then a power of the
central element `v`, whose third coordinate is its length.
-/

open Heisenberg125

open Heis

variable {p : ℕ}

theorem Heisenberg125.Heis.eq_zero_of_cast_eq_zero(hp : 0 < p) {n : ℕ} (hn : n ≤ p - 1)
    (h : (n : ZMod p) = 0) : n = 0 := by sorry
