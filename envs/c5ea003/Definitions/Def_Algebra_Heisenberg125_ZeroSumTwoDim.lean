-- Prove2me | Definitions.Def_Algebra_Heisenberg125_ZeroSumTwoDim
-- name    : Algebra_Heisenberg125_ZeroSumTwoDim
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:20:41.284069+00:00
-- url     : https://prove2.me/theorems/6bce3c56-fb07-41b1-b178-e92e7aff2fd8
-- title:
--   Aether Catalog definitions — Algebra_Heisenberg125_ZeroSumTwoDim
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.Heisenberg125.ZeroSumTwoDim`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/Heisenberg125/ZeroSumTwoDim.lean by skeleton subtraction
import Mathlib
/-
# The Davenport constant of `(ZMod p)^2`: `D(C_p ⊕ C_p) ≤ 2p - 1`

This file proves, by an application of the **Chevalley–Warning theorem**, that
any sequence of `2p - 1` vectors in `(ZMod p)^2` admits a nonempty subsequence
summing to zero (`exists_nonempty_zeroSum_sublist`).

This is the additive-combinatorial engine behind the "line bound" of
`Algebra.Heisenberg125.LineBound`: the preimage in `H_{p^3}` of a line through
the origin of `(ZMod p)^2` is an abelian subgroup isomorphic to `C_p ⊕ C_p`, and
product-one-freeness there is exactly zero-sum-freeness in `(ZMod p)^2`.

The Finset version `exists_nonempty_zeroSum_pair` is stated for two coordinate
functions `u, w : Fin n → ZMod p` so that it can be applied directly to
arbitrary pairs of `ZMod p`-valued statistics of a sequence.
-/

namespace Heisenberg125

open Finset MvPolynomial

variable {p : ℕ} [Fact p.Prime]

/-- The Chevalley–Warning test polynomial `Σ_i u i • X i ^ (p-1)`. -/
private noncomputable def cwPoly {n : ℕ} (u : Fin n → ZMod p) : MvPolynomial (Fin n) (ZMod p) :=
  ∑ i, u i • X i ^ (p - 1)







end Heisenberg125


