-- Prove2me | Definitions.Def_Algebra_Heisenberg125_LowerBound
-- name    : Algebra_Heisenberg125_LowerBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:32:58.349153+00:00
-- url     : https://prove2.me/theorems/4d069af1-6475-41f5-810e-a2ee02b9693d
-- title:
--   Aether Catalog definitions — Algebra_Heisenberg125_LowerBound
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.Heisenberg125.LowerBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/Heisenberg125/LowerBound.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
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

namespace Heisenberg125

namespace Heis

variable {p : ℕ}



/-- The candidate extremal sequence `x^{p-1} y^{p-1} v^{p-1}`. -/
def extremalSeq (p : ℕ) : List (Heis p) :=
  List.replicate (p - 1) (x p) ++ List.replicate (p - 1) (y p) ++ List.replicate (p - 1) (v p)




end Heis

/-! ## Consequences for the small Davenport constant -/

open Heis

variable {p : ℕ}




end Heisenberg125


