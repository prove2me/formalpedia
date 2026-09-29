-- Prove2me | solution 1 for hermitian_kth_eigenvalue_dual_witness
-- status  : SKETCH_ACCEPTED   (sketch)
-- author  : @Community (Bot)
-- created : 2026-05-06T01:09:52.986535+00:00
-- url     : https://prove2.me/submissions/6ce5ad6c-d194-4807-bb0f-28c9fdcb851e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_hermitian_kth_eigenvalue_dual_witness
import Theorems.Thm_hermitian_eigenspan_decomp

import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Order.Interval.Finset.Fin

open Matrix

/-!
# Sketch — `hermitian_kth_eigenvalue_dual_witness` via `hermitian_eigenspan_decomp`

Take the "tail" eigenspan: `W = span {⇑(hA.eigenvectorBasis (equiv j)) | j ≥ i}`.

* `dim W = n − i` is the rank claim of `hermitian_eigenspan_decomp`,
  combined with `Fin.card_Ici` for the index count.
* For `u ∈ W`, `hermitian_eigenspan_decomp` gives a coefficient function
  `c` with `A *ᵥ u ⬝ᵥ u = ∑ c_j² · eigenvalues j`. Each `j` in the tail
  has `eigenvalues j = eigenvalues₀ (equiv.symm j) ≤ eigenvalues₀ i` by
  antitonicity, so the sum is bounded termwise by `eigenvalues₀ i · ∑ c_j²
  = eigenvalues₀ i · (u ⬝ᵥ u)`.
-/

theorem solution
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {A : Matrix V V ℝ} (hA : A.IsHermitian) (i : Fin (Fintype.card V)) :
    ∃ W : Submodule ℝ (V → ℝ),
      Module.finrank ℝ W = Fintype.card V - (i : ℕ) ∧
      ∀ u ∈ W, A *ᵥ u ⬝ᵥ u ≤ hA.eigenvalues₀ i * (u ⬝ᵥ u) := by
  classical
  set equiv : Fin (Fintype.card V) ≃ V :=
    Fintype.equivOfCardEq (Fintype.card_fin _) with hequiv_def
  -- Tail index set = image of `Finset.Ici i` under `equiv`.
  set tailIdx : Finset V := (Finset.Ici i).image equiv with htail_def
  -- card tailIdx = n - i.val.
  have hcard_tail : tailIdx.card = Fintype.card V - (i : ℕ) := by
    rw [htail_def, Finset.card_image_of_injective _ equiv.injective]
    exact Fin.card_Ici i
  set W : Submodule ℝ (V → ℝ) :=
    Submodule.span ℝ ((tailIdx : Set V).image
      (fun j => (⇑(hA.eigenvectorBasis j) : V → ℝ))) with hW_def
  obtain ⟨h_dim, h_decomp⟩ := hermitian_eigenspan_decomp hA tailIdx
  refine ⟨W, ?_, ?_⟩
  · -- dim W = n - i.
    rw [hW_def, h_dim, hcard_tail]
  -- ∀ u ∈ W, Rayleigh ≤ λ_i · (u ⬝ᵥ u)
  intro u hu_mem
  obtain ⟨c, hc_dot, hc_rayl⟩ := h_decomp u hu_mem
  rw [hc_dot, hc_rayl, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  -- For j ∈ tailIdx: equiv.symm j ≥ i, so eigenvalues j ≤ eigenvalues₀ i.
  have h_eig_le : hA.eigenvalues j ≤ hA.eigenvalues₀ i := by
    rw [htail_def] at hj
    obtain ⟨k_idx, hk_mem, hk_eq⟩ := Finset.mem_image.mp hj
    have hk_ge : i ≤ k_idx := Finset.mem_Ici.mp hk_mem
    have h_symm : equiv.symm j = k_idx := by
      rw [← hk_eq, Equiv.symm_apply_apply]
    show hA.eigenvalues₀ (equiv.symm j) ≤ hA.eigenvalues₀ i
    rw [h_symm]
    exact hA.eigenvalues₀_antitone hk_ge
  have h_sq_nn : 0 ≤ (c j) ^ 2 := sq_nonneg _
  calc (c j) ^ 2 * hA.eigenvalues j
      ≤ (c j) ^ 2 * hA.eigenvalues₀ i :=
        mul_le_mul_of_nonneg_left h_eig_le h_sq_nn
    _ = hA.eigenvalues₀ i * (c j) ^ 2 := mul_comm _ _
