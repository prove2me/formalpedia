-- Prove2me | Theorems.Thm_Heisenberg125_exists_nonempty_zeroSum_family
-- name    : Heisenberg125.exists_nonempty_zeroSum_family
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:37:23.529446+00:00
-- url     : https://prove2.me/theorems/61050c35-45cb-4336-9f85-acfd53f244ff
-- title:
--   Davenport constant of `(ZMod p)^k`, Chevalley–Warning form.
-- statement:
--   **Davenport constant of `(ZMod p)^k`, Chevalley–Warning form.**  Given
--   `n > k(p-1)` vectors, described by their `k` coordinate functions
--   `u 0, …, u (k-1) : Fin n → ZMod p`, some nonempty set of indices has all `k`
--   coordinate sums equal to zero.  This is Olson's theorem for elementary abelian
--   `p`-groups: `D((ZMod p)^k) ≤ k(p-1) + 1`.
--
--   ```lean
--   theorem Heisenberg125.exists_nonempty_zeroSum_family{ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
--       (u : ι → Fin n → ZMod p) (hn : Fintype.card ι * (p - 1) < n) :
--       ∃ t : Finset (Fin n), t.Nonempty ∧ ∀ j, ∑ i ∈ t, u j i = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/Heisenberg125/ZeroSumTwoDim.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/Heisenberg125/ZeroSumTwoDim.lean#L43

-- Thm stub generated from Algebra/Heisenberg125/ZeroSumTwoDim.lean
import Mathlib
import Definitions.Def_Algebra_Heisenberg125_ZeroSumTwoDim
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

open Heisenberg125

open Finset MvPolynomial

variable {p : ℕ} [Fact p.Prime]




set_option maxHeartbeats 1000000 in

theorem Heisenberg125.exists_nonempty_zeroSum_family{ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (u : ι → Fin n → ZMod p) (hn : Fintype.card ι * (p - 1) < n) :
    ∃ t : Finset (Fin n), t.Nonempty ∧ ∀ j, ∑ i ∈ t, u j i = 0 := by sorry
