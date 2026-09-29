-- Prove2me | Theorems.Thm_Heisenberg125_productOneFree_piBasisSeq
-- name    : Heisenberg125.productOneFree_piBasisSeq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T18:56:14.364998+00:00
-- url     : https://prove2.me/theorems/619d2152-d299-49b2-b776-3f99b98fab03
-- title:
--   The lower bound.
-- statement:
--   **The lower bound.**  `e_0^{p-1} ⋯ e_{k-1}^{p-1}` is product-one-free.
--
--   ```lean
--   theorem Heisenberg125.productOneFree_piBasisSeq(hp : 1 < p) :
--       ProductOneFree (piBasisSeq p k) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/Heisenberg125/ElementaryAbelian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/Heisenberg125/ElementaryAbelian.lean#L87

-- Thm stub generated from Algebra/Heisenberg125/ElementaryAbelian.lean
import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
import Definitions.Def_Algebra_Heisenberg125_ElementaryAbelian
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

open Heisenberg125

-- open removed: section is not a namespace

variable {p k : ℕ}

/-! ### Two elementary list lemmas -/



/-! ### The standard basis sequence -/

theorem Heisenberg125.productOneFree_piBasisSeq(hp : 1 < p) :
    ProductOneFree (piBasisSeq p k) := by sorry
