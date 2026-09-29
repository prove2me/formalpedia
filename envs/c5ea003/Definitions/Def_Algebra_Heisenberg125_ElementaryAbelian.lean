-- Prove2me | Definitions.Def_Algebra_Heisenberg125_ElementaryAbelian
-- name    : Algebra_Heisenberg125_ElementaryAbelian
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:20:18.438987+00:00
-- url     : https://prove2.me/theorems/bd9289d4-c75d-43ca-90dd-2a5e6a1897c3
-- title:
--   Aether Catalog definitions — Algebra_Heisenberg125_ElementaryAbelian
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.Heisenberg125.ElementaryAbelian`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/Heisenberg125/ElementaryAbelian.lean by skeleton subtraction
import Mathlib
/-
# Olson's theorem for elementary abelian `p`-groups: `d((Z/p)^k) = k(p-1)`

The conjecture of Godara and Sarkar, `d(H_{p^3}) = 3p - 3`, says that the
non-abelian exponent-`p` group of order `p^3` has the *same* small Davenport
constant as the elementary abelian group `(Z/p)^3` of the same order.  This file
proves the abelian half of that statement in full generality:

  `d((Z/p)^k) = k(p - 1)`  for every prime `p` and every `k`.

* the upper bound is the multi-dimensional Chevalley–Warning bound
  `Heisenberg125.exists_nonempty_zeroSum_sublist_family` of
  `Algebra.Heisenberg125.ZeroSumTwoDim` (`D((Z/p)^k) ≤ k(p-1) + 1`);
* the lower bound is the explicit zero-sum-free sequence
  `e_0^{p-1} e_1^{p-1} ⋯ e_{k-1}^{p-1}`, whose zero-sum-freeness is proved by a
  counting argument: the `j`-th coordinate of the sum of a subsequence is the
  multiplicity of `e_j` in it, and multiplicities are bounded by `p - 1`.

For `k = 3` this gives `d((Z/p)^3) = 3p - 3`, and in particular
`d((Z/5)^3) = 12`, exactly the lower bound proved for `H_125`.
-/

namespace Heisenberg125

open Multiplicative

variable {p k : ℕ}

/-! ### Two elementary list lemmas -/



/-! ### The standard basis sequence -/

/-- The `j`-th standard basis vector of `(ZMod p)^k`, viewed multiplicatively. -/
def piBasis (p k : ℕ) (j : Fin k) : Multiplicative (Fin k → ZMod p) :=
  ofAdd (Pi.single j 1)

/-- The candidate extremal sequence `e_0^{p-1} ⋯ e_{k-1}^{p-1}` over
`(ZMod p)^k`. -/
def piBasisSeq (p k : ℕ) : List (Multiplicative (Fin k → ZMod p)) :=
  (List.finRange k).flatMap fun j => List.replicate (p - 1) (piBasis p k j)









end Heisenberg125


