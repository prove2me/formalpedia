-- Prove2me | Theorems.Thm_Heisenberg125_Heis_csum_append
-- name    : Heisenberg125.Heis.csum_append
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:44:27.15439+00:00
-- url     : https://prove2.me/theorems/7f2fad8a-2c0f-4cbd-957a-9208c0af798b
-- title:
--   Csum append
-- statement:
--   Formal statement of `Heisenberg125.Heis.csum_append` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Heisenberg125.Heis.csum_append(L M : List (Heis p)) : csum (L ++ M) = csum L + csum M := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/Heisenberg125/LowerBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/Heisenberg125/LowerBound.lean#L25

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

@[simp]

theorem Heisenberg125.Heis.csum_append(L M : List (Heis p)) : csum (L ++ M) = csum L + csum M := by sorry
