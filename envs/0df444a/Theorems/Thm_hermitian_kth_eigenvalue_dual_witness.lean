-- Prove2me | Theorems.Thm_hermitian_kth_eigenvalue_dual_witness
-- name    : hermitian_kth_eigenvalue_dual_witness
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-03T01:05:00.114212+00:00
-- url     : https://prove2.me/theorems/ed77dd1a-84d6-46a0-97b0-2c293b3b04ca
-- statement:
--   Dual min-max witness (<=) for the i-th descending eigenvalue: there exists a subspace W of (V -> R) of dimension exactly (card V) - i on which the Rayleigh quotient is at most lambda_i for every vector. Naturally satisfied by the eigenvector tail span.
-- source:
--   Huang, Hao. "Induced subgraphs of hypercubes and a proof of the Sensitivity Conjecture." Annals of Mathematics 190.3 (2019): 949-955.

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Real.Star

open Matrix

/-!
# Generalized min-max characterization (upper-bound dual witness form)

For any Hermitian real matrix `A : Matrix V V ℝ` and descending-sorted index
`i`, there exists a subspace `W ⊆ (V → ℝ)` of dimension `(card V) − i` on
which the Rayleigh quotient is bounded above by the `i`-th descending
eigenvalue.

This is the existential, witness-form *dual* min-max characterization
(the other direction of Courant–Fischer): on a `(n − i)`-dim subspace
(natural witness: the span of the bottom `(n − i)` eigenvectors), every
vector's Rayleigh quotient is at most `λ_i`.

Reusable spectral-theory result; not currently in Mathlib in this form.
-/

/-- **Dual min-max witness for the `i`-th descending eigenvalue.**
For any real Hermitian `A : Matrix V V ℝ` and any descending index `i`,
there exists a subspace `W ⊆ (V → ℝ)` of dimension `(card V) − i` such
that every `u ∈ W` has `(A *ᵥ u) ⬝ᵥ u ≤ hA.eigenvalues₀ i * (u ⬝ᵥ u)`. -/

theorem hermitian_kth_eigenvalue_dual_witness
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {A : Matrix V V ℝ} (hA : A.IsHermitian) (i : Fin (Fintype.card V)) :
    ∃ W : Submodule ℝ (V → ℝ),
      Module.finrank ℝ W = Fintype.card V - (i : ℕ) ∧
      ∀ u ∈ W, A *ᵥ u ⬝ᵥ u ≤ hA.eigenvalues₀ i * (u ⬝ᵥ u) := by sorry
