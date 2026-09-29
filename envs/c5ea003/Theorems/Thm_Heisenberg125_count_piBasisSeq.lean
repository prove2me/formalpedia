-- Prove2me | Theorems.Thm_Heisenberg125_count_piBasisSeq
-- name    : Heisenberg125.count_piBasisSeq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:37:25.436808+00:00
-- url     : https://prove2.me/theorems/014144cb-64bf-4d95-9991-5e555afef56a
-- title:
--   Count piBasisSeq
-- statement:
--   Formal statement of `Heisenberg125.count_piBasisSeq` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Heisenberg125.count_piBasisSeq(hp : 1 < p) (j : Fin k) :
--       (piBasisSeq p k).count (piBasis p k j) = p - 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/Heisenberg125/ElementaryAbelian.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/Heisenberg125/ElementaryAbelian.lean#L72

-- Thm stub generated from Algebra/Heisenberg125/ElementaryAbelian.lean
import Mathlib
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

open Multiplicative

variable {p k : ℕ}

/-! ### Two elementary list lemmas -/



/-! ### The standard basis sequence -/

theorem Heisenberg125.count_piBasisSeq(hp : 1 < p) (j : Fin k) :
    (piBasisSeq p k).count (piBasis p k j) = p - 1 := by sorry
