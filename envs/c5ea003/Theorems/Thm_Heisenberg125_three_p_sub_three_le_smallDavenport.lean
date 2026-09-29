-- Prove2me | Theorems.Thm_Heisenberg125_three_p_sub_three_le_smallDavenport
-- name    : Heisenberg125.three_p_sub_three_le_smallDavenport
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:58:35.278365+00:00
-- url     : https://prove2.me/theorems/be602f05-095f-4386-8339-c21af4a281a8
-- title:
--   Lower bound.
-- statement:
--   **Lower bound.**  `d(H_{p^3}) ≥ 3p - 3` for every prime `p` (indeed every `p ≥ 1`).
--
--   ```lean
--   theorem Heisenberg125.three_p_sub_three_le_smallDavenport[NeZero p] :
--       3 * (p - 1) ≤ smallDavenport (Heis p) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/Heisenberg125/LowerBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/Heisenberg125/LowerBound.lean#L93

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








/-! ## Consequences for the small Davenport constant -/

open Heis

variable {p : ℕ}

theorem Heisenberg125.three_p_sub_three_le_smallDavenport[NeZero p] :
    3 * (p - 1) ≤ smallDavenport (Heis p) := by sorry
