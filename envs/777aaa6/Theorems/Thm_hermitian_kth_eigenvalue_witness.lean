-- Prove2me | Theorems.Thm_hermitian_kth_eigenvalue_witness
-- name    : hermitian_kth_eigenvalue_witness
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-05-03T01:04:53.157984+00:00
-- url     : https://prove2.me/theorems/3a59d2a3-c164-449d-a177-3f3f4a07fbf8
-- statement:
--   Min-max witness (>=) for the k-th descending eigenvalue: every subspace W of (V -> R) of dimension at least (card V) - k contains a nonzero v with Rayleigh quotient >= lambda_k. Generalizes Aristole's exists_eigenvector_in_subspace from the specific eigenvalue +sqrt(n).
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
# Generalized min-max characterization (lower-bound witness form)

For any Hermitian real matrix `A : Matrix V V ℝ`, descending-sorted index
`k`, and subspace `W ⊆ (V → ℝ)` whose dimension is at least
`(card V) − k`, there exists a nonzero vector `v ∈ W` whose Rayleigh
quotient is at least the `k`-th descending eigenvalue of `A`.

This is the existential, witness-form *upper-half* min-max characterization
(one direction of Courant–Fischer). It generalizes Aristole's
`exists_eigenvector_in_subspace`, which is the same statement at the
specific eigenvalue `+√n`. Reusable spectral-theory result, not currently
in Mathlib in this form.
-/

/-- **Min-max witness for the `k`-th descending eigenvalue.**
For any real Hermitian `A : Matrix V V ℝ` and any subspace `W ⊆ (V → ℝ)`
with `Module.finrank ℝ W ≥ (card V) − k`, there exists a nonzero `v ∈ W`
whose Rayleigh quotient `(A *ᵥ v ⬝ᵥ v) / (v ⬝ᵥ v)` is at least
`hA.eigenvalues₀ k`. -/

theorem hermitian_kth_eigenvalue_witness
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {A : Matrix V V ℝ} (hA : A.IsHermitian) (k : Fin (Fintype.card V))
    {W : Submodule ℝ (V → ℝ)}
    (hdim : Fintype.card V - (k : ℕ) ≤ Module.finrank ℝ W) :
    ∃ v : V → ℝ, v ∈ W ∧ v ≠ 0 ∧
      hA.eigenvalues₀ k * (v ⬝ᵥ v) ≤ A *ᵥ v ⬝ᵥ v := by sorry
