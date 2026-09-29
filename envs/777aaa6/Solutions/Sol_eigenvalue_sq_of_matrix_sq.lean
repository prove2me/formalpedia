-- Prove2me | solution 1 for eigenvalue_sq_of_matrix_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-04-23T05:11:21.840695+00:00
-- url     : https://prove2.me/submissions/8863df90-f5a0-47a1-86a3-e09ba4856bea

import Theorems.Thm_eigenvalue_sq_of_matrix_sq
import Mathlib.Data.Matrix.Mul

open Matrix

/-!
# Full proof — `eigenvalue_sq_of_matrix_sq`

Terminal leaf. Proof strategy:

* Pick an eigenvector `v := eigenvectorBasis j` for the `j : α` corresponding to
  the sorted index `i`, so `A *ᵥ v = λ • v` (via `mulVec_eigenvectorBasis`).
* Apply `A` twice: `A^2 *ᵥ v = λ^2 • v`.
* From the hypothesis `A^2 = c • 1`: `A^2 *ᵥ v = c • v`.
* `v ≠ 0` (orthonormal basis), so `λ^2 • v = c • v` forces `λ^2 = c`.
-/

theorem solution
    {α : Type*} [Fintype α] [DecidableEq α]
    {A : Matrix α α ℝ} (hA : A.IsHermitian)
    {c : ℝ} (hA_sq : A ^ 2 = c • 1) (i : Fin (Fintype.card α)) :
    (hA.eigenvalues₀ i) ^ 2 = c := by
  -- Bridge `eigenvalues₀ i` to `eigenvalues j` for some `j : α`.
  set j : α := (Fintype.equivOfCardEq (Fintype.card_fin _)) i with hj_def
  have h_eig : hA.eigenvalues j = hA.eigenvalues₀ i := by
    show hA.eigenvalues₀ ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j) =
        hA.eigenvalues₀ i
    congr 1
    rw [hj_def, Equiv.symm_apply_apply]
  rw [← h_eig]
  -- Eigenvector equation.
  have hAv : A *ᵥ ⇑(hA.eigenvectorBasis j) =
      hA.eigenvalues j • ⇑(hA.eigenvectorBasis j) :=
    hA.mulVec_eigenvectorBasis j
  -- `A^2 *ᵥ v = λ^2 • v`.
  have hA2v : (A ^ 2) *ᵥ ⇑(hA.eigenvectorBasis j) =
      (hA.eigenvalues j) ^ 2 • ⇑(hA.eigenvectorBasis j) := by
    calc (A ^ 2) *ᵥ ⇑(hA.eigenvectorBasis j)
        = A *ᵥ (A *ᵥ ⇑(hA.eigenvectorBasis j)) := by
          rw [sq, ← Matrix.mulVec_mulVec]
      _ = A *ᵥ (hA.eigenvalues j • ⇑(hA.eigenvectorBasis j)) := by rw [hAv]
      _ = hA.eigenvalues j • (A *ᵥ ⇑(hA.eigenvectorBasis j)) :=
          Matrix.mulVec_smul _ _ _
      _ = hA.eigenvalues j • (hA.eigenvalues j • ⇑(hA.eigenvectorBasis j)) := by rw [hAv]
      _ = (hA.eigenvalues j) ^ 2 • ⇑(hA.eigenvectorBasis j) := by
          rw [smul_smul, ← sq]
  -- `A^2 *ᵥ v = c • v` from the hypothesis.
  have hA2v' : (A ^ 2) *ᵥ ⇑(hA.eigenvectorBasis j) =
      c • ⇑(hA.eigenvectorBasis j) := by
    rw [hA_sq, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h_smul : (hA.eigenvalues j) ^ 2 • ⇑(hA.eigenvectorBasis j) =
      c • ⇑(hA.eigenvectorBasis j) := hA2v.symm.trans hA2v'
  -- `v ≠ 0`, so scalars match.
  have h_ne : ⇑(hA.eigenvectorBasis j) ≠ 0 :=
    (WithLp.ofLp_eq_zero (p := 2)).ne.mpr
      (hA.eigenvectorBasis.orthonormal.ne_zero j)
  exact smul_left_injective ℝ h_ne h_smul
