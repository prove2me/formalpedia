-- Prove2me | Theorems.Thm_Heisenberg125_exists_nonempty_zeroSum_pair
-- name    : Heisenberg125.exists_nonempty_zeroSum_pair
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:37:40.400092+00:00
-- url     : https://prove2.me/theorems/f066c30c-d6a7-434a-b1b8-b277681e7b37
-- title:
--   Davenport constant of `C_p ⊕ C_p`, Chevalley–Warning form.
-- statement:
--   **Davenport constant of `C_p ⊕ C_p`, Chevalley–Warning form.**  Given
--   `n ≥ 2p - 1` pairs `(u i, w i)` of elements of `ZMod p`, some nonempty set of
--   indices has both coordinate sums equal to zero.
--
--   ```lean
--   theorem Heisenberg125.exists_nonempty_zeroSum_pair{n : ℕ} (u w : Fin n → ZMod p) (hn : 2 * p - 1 ≤ n) :
--       ∃ t : Finset (Fin n), t.Nonempty ∧ ∑ i ∈ t, u i = 0 ∧ ∑ i ∈ t, w i = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/Heisenberg125/ZeroSumTwoDim.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/Heisenberg125/ZeroSumTwoDim.lean#L111

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

theorem Heisenberg125.exists_nonempty_zeroSum_pair{n : ℕ} (u w : Fin n → ZMod p) (hn : 2 * p - 1 ≤ n) :
    ∃ t : Finset (Fin n), t.Nonempty ∧ ∑ i ∈ t, u i = 0 ∧ ∑ i ∈ t, w i = 0 := by sorry
